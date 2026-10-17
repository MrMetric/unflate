//! Shared DEFLATE primitives: LSB-first bit I/O, canonical Huffman coding,
//! RFC 1951 tables, and CL sequence parsing.

const std = @import("std");

// ── RFC 1951 constant tables ────────────────────────────────────────────────

// (base_length, extra_bits) for length codes 257..285
pub const LEN_BASE = [_]u16{ 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258 };
pub const LEN_EXTRA = [_]u3{ 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0 };

// (base_dist, extra_bits) for distance codes 0..29
pub const DIST_BASE = [_]u16{ 1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577 };
pub const DIST_EXTRA = [_]u4{ 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13 };

// HCLEN permutation order
pub const HCLEN_ORDER = [_]u5{ 16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15 };

pub const PNG_SIG = [_]u8{ 0x89, 'P', 'N', 'G', '\r', '\n', 0x1a, '\n' };

pub const ERR: i64 = -1;
pub const MAX_SYMS = 288; // literal/length alphabet upper bound

/// Offset of a supported compressed PNG auxiliary payload. All preceding
/// fields are metadata and must survive byte-for-byte. Uncompressed iTXt,
/// unknown methods/types and truncated prefixes have no optimizable stream.
pub fn pngCompressedOffset(typ: []const u8, data: []const u8) ?usize {
	const international = std.mem.eql(u8, typ, "iTXt");
	if (!international and !std.mem.eql(u8, typ, "zTXt") and !std.mem.eql(u8, typ, "iCCP")) return null;
	const nul = std.mem.indexOfScalar(u8, data, 0) orelse return null;
	if (!international) {
		if (nul + 2 > data.len or data[nul + 1] != 0) return null;
		return nul + 2;
	}
	if (nul + 3 > data.len or data[nul + 1] != 1 or data[nul + 2] != 0) return null;
	var pos = nul + 3;
	for (0..2) |_| { // language tag and translated keyword
		pos = (std.mem.indexOfScalarPos(u8, data, pos, 0) orelse return null) + 1;
	}
	return pos;
}

// ── bit reader ──────────────────────────────────────────────────────────────

/// LSB-first bit reader with zero-fill past end (RFC 1951 §3.1 LSB-first).
pub const BitReader = struct {
	data: []const u8,
	buf: u64 = 0,
	cnt: u32 = 0,
	byte: usize = 0, // index of next source byte to pull

	fn fill(self: *BitReader, n: u32) void {
		while (self.cnt < n) {
			if (self.byte < self.data.len) {
				self.buf |= @as(u64, self.data[self.byte]) << @intCast(self.cnt);
			}
			self.byte += 1;
			self.cnt += 8;
		}
	}

	/// Return the next n bits without advancing the logical cursor. Filling may
	/// pull real or zero-filled bytes into the buffer, but pos() is unchanged.
	fn peek(self: *BitReader, n: u32) u32 {
		if (self.cnt < n) self.fill(n);
		const mask: u64 = (@as(u64, 1) << @intCast(n)) - 1;
		return @intCast(self.buf & mask);
	}

	fn consume(self: *BitReader, n: u32) void {
		self.buf >>= @intCast(n);
		self.cnt -= n;
	}

	/// Read n bits (n <= 16). Zero-fills past end of data.
	pub fn read(self: *BitReader, n: u32) u32 {
		const v = self.peek(n);
		self.consume(n);
		return v;
	}

	pub fn byteAlign(self: *BitReader) void {
		const drop = self.cnt & 7;
		self.buf >>= @intCast(drop);
		self.cnt -= drop;
	}

	/// Skip n whole bytes; reader must be byte-aligned. Returns false if this
	/// would read past end of data (truncated → caller errors).
	pub fn skipBytes(self: *BitReader, n: usize) bool {
		// Buffered lookahead can include synthetic bytes past EOF.
		if (n > self.realAvail()) return false;
		var remaining = n;
		// Drain whole bytes already buffered.
		while (self.cnt >= 8 and remaining > 0) {
			self.buf >>= 8;
			self.cnt -= 8;
			remaining -= 1;
		}
		if (remaining > 0) {
			if (self.byte + remaining > self.data.len) return false;
			self.byte += remaining;
		}
		return true;
	}

	/// Absolute bit offset consumed so far.
	pub fn pos(self: *const BitReader) usize {
		return self.byte * 8 - self.cnt;
	}

	/// Real (non-zero-filled) bytes remaining from the current position.
	/// Reader must be byte-aligned (cnt a multiple of 8). Buffered-but-unconsumed
	/// bytes (cnt/8) were already pulled from data, so subtract them from byte.
	pub fn realAvail(self: *const BitReader) usize {
		const consumed = self.byte - self.cnt / 8;
		return if (consumed >= self.data.len) 0 else self.data.len - consumed;
	}

	/// Read n whole bytes into out[0..n]; reader must be byte-aligned. Returns
	/// false if this would read past end of real data (truncated).
	pub fn readBytes(self: *BitReader, out: []u8) bool {
		if (out.len > self.realAvail()) return false;
		for (out) |*b| {
			if (self.cnt >= 8) {
				b.* = @intCast(self.buf & 0xff);
				self.buf >>= 8;
				self.cnt -= 8;
			} else {
				if (self.byte >= self.data.len) return false;
				b.* = self.data[self.byte];
				self.byte += 1;
			}
		}
		return true;
	}

	/// True if the next symbol would start at or past end of data.
	pub fn atEnd(self: *const BitReader) bool {
		// bits remaining available = data.len*8 - pos()
		return self.pos() >= self.data.len * 8;
	}
};

// ── bit writer ──────────────────────────────────────────────────────────────

/// LSB-first bit writer (RFC 1951 §3.1). Bits are packed
/// least-significant first; Huffman codes are pushed MSB-first by the caller via
/// writeCode. Backed by a caller-supplied ArrayList + allocator.
pub const BitWriter = struct {
	out: *std.ArrayList(u8),
	alloc: std.mem.Allocator,
	buf: u64 = 0,
	cnt: u6 = 0, // bits currently buffered (< 8 after every flush)
	nbits: usize = 0, // total bits written

	pub fn init(out: *std.ArrayList(u8), alloc: std.mem.Allocator) BitWriter {
		return .{ .out = out, .alloc = alloc };
	}

	/// Write n low bits of v, LSB-first.
	pub fn writeBits(self: *BitWriter, v: u32, n: u32) !void {
		if (n == 0) return;
		self.buf |= @as(u64, v & ((@as(u64, 1) << @intCast(n)) - 1)) << @intCast(self.cnt);
		self.cnt += @intCast(n);
		self.nbits += n;
		while (self.cnt >= 8) {
			try self.out.append(self.alloc, @intCast(self.buf & 0xff));
			self.buf >>= 8;
			self.cnt -= 8;
		}
	}

	/// Write a Huffman code of `len` bits, MSB-first (code's high bit emitted
	/// first into the LSB-first stream). Matches deflasm canonical assembly.
	pub fn writeCode(self: *BitWriter, code: u32, len: u32) !void {
		var i: u32 = len;
		while (i > 0) {
			i -= 1;
			try self.writeBits((code >> @intCast(i)) & 1, 1);
		}
	}

	/// Pad with zero bits to the next byte boundary.
	pub fn alignByte(self: *BitWriter) !void {
		if (self.cnt & 7 != 0) {
			const pad = 8 - (self.cnt & 7);
			try self.writeBits(0, pad);
		}
	}

	/// Append whole bytes; writer must be byte-aligned.
	pub fn writeBytes(self: *BitWriter, bytes: []const u8) !void {
		std.debug.assert(self.cnt == 0);
		try self.out.appendSlice(self.alloc, bytes);
		self.nbits += bytes.len * 8;
	}

	pub fn totalBits(self: *const BitWriter) usize {
		return self.nbits;
	}
};

// ── canonical Huffman decoder ───────────────────────────────────────────────

const HUFF_FAST_BITS: u32 = 9;
const HUFF_FAST_SYM_BITS: u4 = 9;
const HUFF_FAST_SIZE = 1 << HUFF_FAST_BITS;
const HUFF_FAST_SYM_MASK = (1 << HUFF_FAST_SYM_BITS) - 1;

pub const HuffDec = struct {
	max_len: u32 = 0,
	count: [16]u32 = [_]u32{0} ** 16,
	first_code: [16]u32 = [_]u32{0} ** 16,
	first_sym: [16]u32 = [_]u32{0} ** 16, // offset into syms[]
	syms: [MAX_SYMS]u16 = undefined,
	n_syms: u32 = 0,
	// Packed (code length, symbol+1), indexed by the next HUFF_FAST_BITS raw
	// LSB-first stream bits. Zero means the prefix needs the canonical walk.
	fast: [HUFF_FAST_SIZE]u16 = [_]u16{0} ** HUFF_FAST_SIZE,

	/// Build from code lengths. Returns null on over-complete code (Kraft sum
	/// strictly greater than the full code space).
	/// An all-zero / empty table builds with max_len == 0.
	pub fn build(lengths: []const u8) ?HuffDec {
		var h = HuffDec{};
		var max_len: u32 = 0;
		for (lengths) |l| {
			if (l > 0) {
				h.count[l] += 1;
				if (l > max_len) max_len = l;
			}
		}
		h.max_len = max_len;
		if (max_len == 0) return h; // empty table

		// Kraft inequality: sum 2^(max-len) <= 2^max. Over-complete → error.
		var kraft: u64 = 0;
		var len: u32 = 1;
		while (len <= max_len) : (len += 1) {
			kraft += @as(u64, h.count[len]) << @intCast(max_len - len);
		}
		if (kraft > (@as(u64, 1) << @intCast(max_len))) return null;

		// Canonical code assignment (RFC 1951 §3.2.2).
		var next_code: [16]u32 = [_]u32{0} ** 16;
		var code: u32 = 0;
		var bits: u32 = 1;
		while (bits <= max_len) : (bits += 1) {
			code = (code + h.count[bits - 1]) << 1;
			next_code[bits] = code;
			h.first_code[bits] = code;
		}
		// Symbols ordered by (length asc, symbol asc) — canonical order.
		var offset: [16]u32 = [_]u32{0} ** 16;
		var acc: u32 = 0;
		len = 1;
		while (len <= max_len) : (len += 1) {
			h.first_sym[len] = acc;
			offset[len] = acc;
			acc += h.count[len];
		}
		h.n_syms = acc;
		for (lengths, 0..) |l, sym| {
			if (l > 0) {
				h.syms[offset[l]] = @intCast(sym);
				offset[l] += 1;

				const sym_code = next_code[l];
				next_code[l] += 1;
				if (l <= HUFF_FAST_BITS) {
					// Canonical codes are consumed MSB-first, while peek()
					// exposes the stream's first bit in bit 0.
					var raw: u32 = 0;
					var bit: u32 = 0;
					while (bit < l) : (bit += 1) {
						raw |= ((sym_code >> @intCast(l - bit - 1)) & 1) << @intCast(bit);
					}
					const fast_entry: u16 = (@as(u16, l) << HUFF_FAST_SYM_BITS) |
						@as(u16, @intCast(sym + 1));
					const suffix_count: u32 = @as(u32, 1) << @intCast(HUFF_FAST_BITS - l);
					var suffix: u32 = 0;
					while (suffix < suffix_count) : (suffix += 1) {
						h.fast[raw | (suffix << @intCast(l))] = fast_entry;
					}
				}
			}
		}
		return h;
	}

	fn decodeCanonical(self: *const HuffDec, r: *BitReader) ?u16 {
		var code: u32 = 0;
		var len: u32 = 1;
		while (len <= self.max_len) : (len += 1) {
			code = (code << 1) | r.read(1);
			if (self.count[len] != 0) {
				const rel = code -% self.first_code[len];
				if (rel < self.count[len]) {
					return self.syms[self.first_sym[len] + rel];
				}
			}
		}
		return null;
	}

	/// Decode one symbol. Short codes use a raw-bit prefix table; unresolved
	/// prefixes retain the canonical one-bit walk so invalid/truncated inputs
	/// fail after exactly the same number of consumed bits as before.
	pub fn decode(self: *const HuffDec, r: *BitReader) ?u16 {
		const fast_entry = self.fast[r.peek(HUFF_FAST_BITS)];
		if (fast_entry != 0) {
			const len: u32 = fast_entry >> HUFF_FAST_SYM_BITS;
			r.consume(len);
			return @intCast((fast_entry & HUFF_FAST_SYM_MASK) - 1);
		}
		return self.decodeCanonical(r);
	}
};

// Fixed Huffman tables (RFC 1951 §3.2.6).
pub fn fixedLL() HuffDec {
	@setEvalBranchQuota(10000);
	var lengths: [288]u8 = undefined;
	var i: usize = 0;
	while (i < 144) : (i += 1) lengths[i] = 8;
	while (i < 256) : (i += 1) lengths[i] = 9;
	while (i < 280) : (i += 1) lengths[i] = 7;
	while (i < 288) : (i += 1) lengths[i] = 8;
	return HuffDec.build(&lengths).?;
}

pub fn fixedDist() HuffDec {
	@setEvalBranchQuota(10000);
	const lengths = [_]u8{5} ** 32;
	return HuffDec.build(&lengths).?;
}

/// Comptime-built shared fixed tables — call sites use these instead of
/// rebuilding the decoders per block/member.
pub const fixed_ll_dec = fixedLL();
pub const fixed_dist_dec = fixedDist();

fn testRand(state: *u64) u64 {
	state.* = state.* *% 6364136223846793005 +% 1442695040888963407;
	return state.*;
}

fn testConsumePrefix(r: *BitReader, n: u32) void {
	var left = n;
	while (left > 0) {
		const take = @min(left, 16);
		_ = r.read(take);
		left -= take;
	}
}

fn testDecoderParity(lengths: []const u8, state: *u64) !void {
	const h = HuffDec.build(lengths).?;
	var case: usize = 0;
	while (case < 64) : (case += 1) {
		var bytes: [8]u8 = undefined;
		for (&bytes) |*b| b.* = @truncate(testRand(state));
		const data_len: usize = @intCast(testRand(state) % (bytes.len + 1));
		const prefix: u32 = @intCast(testRand(state) % (data_len * 8 + 13));
		var fast = BitReader{ .data = bytes[0..data_len] };
		var canonical = BitReader{ .data = bytes[0..data_len] };
		testConsumePrefix(&fast, prefix);
		testConsumePrefix(&canonical, prefix);

		const fast_sym = h.decode(&fast);
		const canonical_sym = h.decodeCanonical(&canonical);
		try std.testing.expectEqual(canonical_sym, fast_sym);
		try std.testing.expectEqual(canonical.pos(), fast.pos());
		try std.testing.expectEqual(canonical.atEnd(), fast.atEnd());
		if (fast.pos() & 7 == 0) {
			try std.testing.expectEqual(canonical.realAvail(), fast.realAvail());
		}

		// A lookup may prefetch bytes, so compare subsequent logical reads
		// rather than private buffer shape. This also exercises zero fill.
		for ([_]u32{ 1, 3, 8, 16 }) |n| {
			try std.testing.expectEqual(canonical.read(n), fast.read(n));
			try std.testing.expectEqual(canonical.pos(), fast.pos());
		}
	}
}

test "HuffDec prefix table matches canonical walk on valid and truncated inputs" {
	var state: u64 = 0x6a34_d4e8_3a00_0001;

	try testDecoderParity(&([_]u8{0} ** 19), &state);
	var singleton = [_]u8{0} ** 19;
	singleton[7] = 1;
	try testDecoderParity(&singleton, &state);
	var long_incomplete = [_]u8{0} ** MAX_SYMS;
	for ([_]u8{ 1, 3, 4, 9, 10, 15 }, 0..) |len, sym| long_incomplete[sym] = len;
	try testDecoderParity(&long_incomplete, &state);
	var fixed_ll_lengths = [_]u8{0} ** 288;
	var fixed_i: usize = 0;
	while (fixed_i < 144) : (fixed_i += 1) fixed_ll_lengths[fixed_i] = 8;
	while (fixed_i < 256) : (fixed_i += 1) fixed_ll_lengths[fixed_i] = 9;
	while (fixed_i < 280) : (fixed_i += 1) fixed_ll_lengths[fixed_i] = 7;
	while (fixed_i < 288) : (fixed_i += 1) fixed_ll_lengths[fixed_i] = 8;
	try testDecoderParity(&fixed_ll_lengths, &state);
	try testDecoderParity(&([_]u8{5} ** 32), &state);

	// Generate complete prefix trees by repeatedly splitting a leaf, shuffle
	// their code lengths across symbols, and sometimes remove one leaf to
	// cover incomplete tables. The canonical walk is the pre-table oracle.
	var tree: usize = 0;
	while (tree < 128) : (tree += 1) {
		var leaves = [_]u8{0} ** MAX_SYMS;
		leaves[0] = 1;
		leaves[1] = 1;
		var n_leaves: usize = 2;
		const split_count: usize = @intCast(testRand(&state) % 96);
		var split: usize = 0;
		while (split < split_count and n_leaves < MAX_SYMS) : (split += 1) {
			var idx: usize = @intCast(testRand(&state) % n_leaves);
			var scanned: usize = 0;
			while (leaves[idx] == 15 and scanned < n_leaves) : (scanned += 1) {
				idx = (idx + 1) % n_leaves;
			}
			if (scanned == n_leaves) break;
			leaves[idx] += 1;
			leaves[n_leaves] = leaves[idx];
			n_leaves += 1;
		}
		if (tree & 1 == 1 and n_leaves > 1) n_leaves -= 1;

		var lengths = [_]u8{0} ** MAX_SYMS;
		@memcpy(lengths[0..n_leaves], leaves[0..n_leaves]);
		var i: usize = lengths.len;
		while (i > 1) {
			i -= 1;
			const j: usize = @intCast(testRand(&state) % (i + 1));
			std.mem.swap(u8, &lengths[i], &lengths[j]);
		}
		try testDecoderParity(&lengths, &state);
	}
}

// ── canonical Huffman encoder ───────────────────────────────────────────────

/// Canonical Huffman encoder: maps symbol → (code, len) for assembly. Built
/// from code lengths exactly like the decoder's canonical assignment, but keeps
/// per-symbol code/len so the writer can emit them. A length-0 symbol has
/// len == 0 (absent).
pub fn HuffEnc(comptime n: usize) type {
	return struct {
		const Self = @This();
		code: [n]u32 = [_]u32{0} ** n,
		len: [n]u8 = [_]u8{0} ** n,

		/// Build from `lengths` (len <= n). Returns null on over-complete code.
		pub fn build(lengths: []const u8) ?Self {
			var self = Self{};
			var count: [16]u32 = [_]u32{0} ** 16;
			var max_len: u32 = 0;
			for (lengths) |l| {
				if (l > 0) {
					count[l] += 1;
					if (l > max_len) max_len = l;
				}
			}
			if (max_len == 0) return self; // empty table

			var kraft: u64 = 0;
			var len: u32 = 1;
			while (len <= max_len) : (len += 1) {
				kraft += @as(u64, count[len]) << @intCast(max_len - len);
			}
			if (kraft > (@as(u64, 1) << @intCast(max_len))) return null;

			var next_code: [16]u32 = [_]u32{0} ** 16;
			var code: u32 = 0;
			var bits: u32 = 1;
			while (bits <= max_len) : (bits += 1) {
				code = (code + count[bits - 1]) << 1;
				next_code[bits] = code;
			}
			for (lengths, 0..) |l, sym| {
				if (l > 0) {
					self.code[sym] = next_code[l];
					self.len[sym] = @intCast(l);
					next_code[l] += 1;
				}
			}
			return self;
		}

		/// Bit length of symbol's code (0 if absent).
		pub fn bitLen(self: *const Self, sym: usize) u8 {
			return self.len[sym];
		}
	};
}

// ── O(1) length/distance code lookup ────────────────────────────────────────

/// length (3..258) → (code 257..285, extra_bits). Index 0..2 unused.
pub const LenCode = struct { code: u16, extra: u3 };
pub const lenCodeTable: [259]LenCode = blk: {
	var t: [259]LenCode = undefined;
	var i: usize = 0;
	while (i < LEN_BASE.len) : (i += 1) {
		const base = LEN_BASE[i];
		const end = if (i + 1 < LEN_BASE.len) LEN_BASE[i + 1] else base + 1;
		var n: usize = base;
		while (n < end) : (n += 1) t[n] = .{ .code = @intCast(257 + i), .extra = LEN_EXTRA[i] };
	}
	break :blk t;
};

/// distance (1..32768) → (code 0..29, extra_bits). Index 0 unused.
pub const DistCode = struct { code: u16, extra: u4 };
pub const distCodeTable: [32769]DistCode = blk: {
	@setEvalBranchQuota(200000);
	var t: [32769]DistCode = undefined;
	var i: usize = 0;
	while (i < DIST_BASE.len) : (i += 1) {
		const base = DIST_BASE[i];
		const end = if (i + 1 < DIST_BASE.len) DIST_BASE[i + 1] else 32769;
		var d: usize = base;
		while (d < end) : (d += 1) t[d] = .{ .code = @intCast(i), .extra = DIST_EXTRA[i] };
	}
	break :blk t;
};

// ── CL code-length sequence parser ──────────────────────────────────────────

/// Parse `n` code lengths from a CL Huffman stream into out[0..n].
/// Returns false on a malformed sequence.
pub fn parseClLengths(r: *BitReader, cl: *const HuffDec, out: []u8, n: usize) bool {
	var i: usize = 0;
	while (i < n) {
		const sym = cl.decode(r) orelse return false;
		if (sym <= 15) {
			out[i] = @intCast(sym);
			i += 1;
		} else if (sym == 16) {
			if (i == 0) return false; // copy-previous at start
			const count = r.read(2) + 3;
			const prev = out[i - 1];
			var c: u32 = 0;
			while (c < count and i < n) : (c += 1) {
				out[i] = prev;
				i += 1;
			}
			if (c < count) return false; // ran past alphabet → malformed
		} else if (sym == 17) {
			const count = r.read(3) + 3;
			var c: u32 = 0;
			while (c < count and i < n) : (c += 1) {
				out[i] = 0;
				i += 1;
			}
			if (c < count) return false;
		} else if (sym == 18) {
			const count = r.read(7) + 11;
			var c: u32 = 0;
			while (c < count and i < n) : (c += 1) {
				out[i] = 0;
				i += 1;
			}
			if (c < count) return false;
		} else {
			return false;
		}
	}
	return true;
}

test "byte reads reject synthetic lookahead bytes" {
	const h = HuffDec.build(&.{1}).?;
	const data = [_]u8{ 0, 0xa5, 0x5a };
	for (1..4) |data_len| {
		for (0..4) |n| {
			var r = BitReader{ .data = data[0..data_len] };
			try std.testing.expectEqual(@as(?u16, 0), h.decode(&r));
			r.byteAlign();
			var out: [3]u8 = undefined;
			const ok = r.readBytes(out[0..n]);
			try std.testing.expectEqual(n <= data_len - 1, ok);
			if (ok) {
				try std.testing.expectEqualSlices(u8, data[1 .. 1 + n], out[0..n]);
				try std.testing.expectEqual((1 + n) * 8, r.pos());
			}
		}
	}
}

test "byte skips reject synthetic lookahead bytes" {
	const h = HuffDec.build(&.{1}).?;
	const data = [_]u8{ 0, 0xa5, 0x5a };
	for (1..4) |data_len| {
		for (0..4) |n| {
			var r = BitReader{ .data = data[0..data_len] };
			try std.testing.expectEqual(@as(?u16, 0), h.decode(&r));
			r.byteAlign();
			const ok = r.skipBytes(n);
			try std.testing.expectEqual(n <= data_len - 1, ok);
			if (ok) try std.testing.expectEqual((1 + n) * 8, r.pos());
		}
	}
}
