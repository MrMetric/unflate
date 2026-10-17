//! DEFLATE parser and assembler. Blocks retain tokens, Huffman lengths,
//! CL RLE entries and original spelling details for bit-exact roundtrips.
//! Also handles gzip headers and ZIP structure; PNG handling is in deflopt.zig.

const std = @import("std");
const common = @import("deflcommon.zig");

const BitReader = common.BitReader;
const BitWriter = common.BitWriter;
const HuffDec = common.HuffDec;
const HuffEnc = common.HuffEnc;
const parseClLengths = common.parseClLengths;
const LEN_BASE = common.LEN_BASE;
const LEN_EXTRA = common.LEN_EXTRA;
const DIST_BASE = common.DIST_BASE;
const DIST_EXTRA = common.DIST_EXTRA;
const HCLEN_ORDER = common.HCLEN_ORDER;
const lenCodeTable = common.lenCodeTable;
const distCodeTable = common.distCodeTable;

pub const ParseError = error{ Malformed, OutOfMemory };

// ── IR ──────────────────────────────────────────────────────────────────────

pub const Match = struct { length: u16, distance: u16, original_alt258: bool = false };

pub const BitPadding = struct { width: u3, value: u8 };
pub const HuffEncoding = struct {
	hclen: u8 = 0,
	final_padding: ?BitPadding = null,
};

pub const Token = union(enum) {
	lit: u8,
	match: Match,
};

pub const ClKind = enum(u8) { lit, rep16, rep17, rep18, sep };
pub const ClEntry = struct { kind: ClKind, val: u16 };

pub const Huff = struct {
	is_fixed: bool,
	tokens: []const Token,
	ll_lengths: []u8, // hlit entries (dynamic only)
	dist_lengths: []u8, // hdist entries (dynamic only)
	cl_lengths: [19]u8, // 19 CL code lengths, symbol order
	cl_entries: []ClEntry, // exact RLE incl. one .sep between ll and dist
	encoding: ?HuffEncoding = null, // new/rebuilt blocks use normal reconstruction
};

pub const BlockBody = union(enum) {
	stored: []const u8,
	huff: Huff,
};

pub const Block = struct {
	is_last: bool,
	body: BlockBody,
	alignment_padding: ?BitPadding = null, // stored blocks only
};

// Fixed Huffman code lengths (RFC 1951 §3.2.6).
const fixed_ll_lengths: [288]u8 = blk: {
	var a: [288]u8 = undefined;
	var i: usize = 0;
	while (i < 144) : (i += 1) a[i] = 8;
	while (i < 256) : (i += 1) a[i] = 9;
	while (i < 280) : (i += 1) a[i] = 7;
	while (i < 288) : (i += 1) a[i] = 8;
	break :blk a;
};
const fixed_dist_lengths = [_]u8{5} ** 32;

// Comptime-built fixed-table encoders (assemble side; the decode side uses
// common.fixed_ll_dec / common.fixed_dist_dec) — no per-block rebuilds.
const fixed_ll_enc = HuffEnc(288).build(&fixed_ll_lengths).?;
const fixed_dist_enc = HuffEnc(32).build(&fixed_dist_lengths).?;

// ── parsing ─────────────────────────────────────────────────────────────────

/// Parse `n` CL code lengths into out[0..n], appending the exact RLE entries.
fn parseClSeq(
	r: *BitReader,
	cl: *const HuffDec,
	out: []u8,
	n: usize,
	entries: *std.ArrayList(ClEntry),
	alloc: std.mem.Allocator,
) ParseError!void {
	var i: usize = 0;
	while (i < n) {
		const sym = cl.decode(r) orelse return error.Malformed;
		if (sym <= 15) {
			out[i] = @intCast(sym);
			i += 1;
			try entries.append(alloc, .{ .kind = .lit, .val = sym });
		} else if (sym == 16) {
			if (i == 0) return error.Malformed; // copy-previous at start
			const count = r.read(2) + 3;
			const prev = out[i - 1];
			var c: u32 = 0;
			while (c < count) : (c += 1) {
				if (i >= n) return error.Malformed; // overshoot (spanning repeat)
				out[i] = prev;
				i += 1;
			}
			try entries.append(alloc, .{ .kind = .rep16, .val = @intCast(count) });
		} else if (sym == 17) {
			const count = r.read(3) + 3;
			var c: u32 = 0;
			while (c < count) : (c += 1) {
				if (i >= n) return error.Malformed;
				out[i] = 0;
				i += 1;
			}
			try entries.append(alloc, .{ .kind = .rep17, .val = @intCast(count) });
		} else if (sym == 18) {
			const count = r.read(7) + 11;
			var c: u32 = 0;
			while (c < count) : (c += 1) {
				if (i >= n) return error.Malformed;
				out[i] = 0;
				i += 1;
			}
			try entries.append(alloc, .{ .kind = .rep18, .val = @intCast(count) });
		} else {
			return error.Malformed;
		}
	}
}

/// Decode the token stream of a Huffman block up to EOB into `tokens`.
fn parseTokens(
	r: *BitReader,
	ll: *const HuffDec,
	dist: *const HuffDec,
	tokens: *std.ArrayList(Token),
	alloc: std.mem.Allocator,
) ParseError!void {
	while (true) {
		if (r.atEnd()) return error.Malformed; // symbol would start past end
		const sym = ll.decode(r) orelse return error.Malformed;
		if (sym < 256) {
			try tokens.append(alloc, .{ .lit = @intCast(sym) });
			continue;
		}
		if (sym == 256) return; // EOB
		if (sym > 285) return error.Malformed;
		const mlen: u16 = @intCast(LEN_BASE[sym - 257] + r.read(LEN_EXTRA[sym - 257]));
		const dsym = dist.decode(r) orelse return error.Malformed;
		if (dsym > 29) return error.Malformed;
		const mdist: u16 = @intCast(DIST_BASE[dsym] + r.read(DIST_EXTRA[dsym]));
		try tokens.append(alloc, .{ .match = .{
			.length = mlen, .distance = mdist, .original_alt258 = sym == 284 and mlen == 258,
		} });
	}
}

pub fn parseBlock(r: *BitReader, alloc: std.mem.Allocator) ParseError!Block {
	var block = try parseBlockInner(r, alloc);
	// Huffman lookahead may zero-fill, but no block may consume those bits.
	if (r.pos() > r.data.len * 8) return error.Malformed;
	if (block.is_last and block.body == .huff) {
		const width: u3 = @intCast((8 - (r.pos() & 7)) & 7);
		const value: u8 = if (width == 0) 0 else r.data[r.pos() / 8] >> @as(u3, @intCast(r.pos() & 7));
		block.body.huff.encoding.?.final_padding = .{ .width = width, .value = value };
	}
	return block;
}

fn parseBlockInner(r: *BitReader, alloc: std.mem.Allocator) ParseError!Block {
	const is_last = r.read(1) == 1;
	const btype = r.read(2);

	if (btype == 0) { // stored
		const width: u3 = @intCast((8 - (r.pos() & 7)) & 7);
		const padding = BitPadding{ .width = width, .value = @intCast(r.read(width)) };
		if (r.realAvail() < 4) return error.Malformed;
		var hdr: [4]u8 = undefined;
		if (!r.readBytes(&hdr)) return error.Malformed;
		const len: usize = @as(usize, hdr[0]) | (@as(usize, hdr[1]) << 8);
		const nlen: usize = @as(usize, hdr[2]) | (@as(usize, hdr[3]) << 8);
		if (nlen != len ^ 0xFFFF) return error.Malformed;
		if (r.realAvail() < len) return error.Malformed;
		const data = try alloc.alloc(u8, len);
		if (!r.readBytes(data)) return error.Malformed;
		return .{ .is_last = is_last, .body = .{ .stored = data }, .alignment_padding = padding };
	}

	if (btype == 1) { // fixed Huffman
		var tokens: std.ArrayList(Token) = .empty;
		try parseTokens(r, &common.fixed_ll_dec, &common.fixed_dist_dec, &tokens, alloc);
		return .{ .is_last = is_last, .body = .{ .huff = .{
			.is_fixed = true,
			.tokens = tokens.items,
			.ll_lengths = &.{},
			.dist_lengths = &.{},
			.cl_lengths = [_]u8{0} ** 19,
			.cl_entries = &.{},
			.encoding = .{},
		} } };
	}

	if (btype == 2) { // dynamic Huffman
		const hlit = r.read(5) + 257;
		const hdist = r.read(5) + 1;
		const hclen = r.read(4) + 4;
		if (hlit > 286) return error.Malformed;

		var cl_raw = [_]u8{0} ** 19;
		var i: usize = 0;
		while (i < hclen) : (i += 1) cl_raw[HCLEN_ORDER[i]] = @intCast(r.read(3));
		const cl = HuffDec.build(&cl_raw) orelse return error.Malformed;

		// RFC 1951 §3.2.7: lit/len and distance code lengths are ONE shared
		// run-length sequence of hlit+hdist values; a repeat code (16/17/18) may
		// straddle the hlit boundary, so decode the whole sequence in one pass.
		// Decoding hlit then hdist separately mis-handles a crossing repeat (it
		// overshoots into phantom lit/len symbols).
		const combined = try alloc.alloc(u8, hlit + hdist);
		var entries: std.ArrayList(ClEntry) = .empty;
		try parseClSeq(r, &cl, combined, hlit + hdist, &entries, alloc);
		const ll_lengths = combined[0..hlit];
		const dist_lengths = combined[hlit .. hlit + hdist];

		// Insert .sep when CL entries split cleanly at the literal/distance
		// boundary. A crossing repeat keeps the sequence flat; assembly ignores
		// .sep, so either representation preserves the same bits.
		var acc: usize = 0;
		for (entries.items, 0..) |e, idx| {
			if (acc == hlit) {
				try entries.insert(alloc, idx, .{ .kind = .sep, .val = 0 });
				break;
			}
			const n: usize = if (e.kind == .lit) 1 else e.val;
			if (acc < hlit and hlit < acc + n) break; // crossing repeat → flat
			acc += n;
		}

		const ll = HuffDec.build(ll_lengths) orelse return error.Malformed;
		const dist = HuffDec.build(dist_lengths) orelse return error.Malformed;
		var tokens: std.ArrayList(Token) = .empty;
		try parseTokens(r, &ll, &dist, &tokens, alloc);

		return .{ .is_last = is_last, .body = .{ .huff = .{
			.is_fixed = false,
			.tokens = tokens.items,
			.ll_lengths = ll_lengths,
			.dist_lengths = dist_lengths,
			.cl_lengths = cl_raw,
			.cl_entries = entries.items,
			.encoding = .{ .hclen = @intCast(hclen) },
		} } };
	}

	return error.Malformed; // reserved BTYPE 3
}

pub fn parseDeflate(alloc: std.mem.Allocator, data: []const u8) ParseError![]Block {
	var consumed: usize = undefined;
	return parseDeflateConsumed(alloc, data, &consumed);
}

/// Like parseDeflate, also report consumed bytes (round the final bit up
/// to a byte). Container callers use this to locate the following trailer.
pub fn parseDeflateConsumed(alloc: std.mem.Allocator, data: []const u8, consumed_bytes: *usize) ParseError![]Block {
	var r = BitReader{ .data = data };
	var blocks: std.ArrayList(Block) = .empty;
	while (true) {
		const b = try parseBlock(&r, alloc);
		try blocks.append(alloc, b);
		if (b.is_last) break;
	}
	consumed_bytes.* = (r.pos() + 7) / 8;
	return blocks.items;
}

// ── assembly ────────────────────────────────────────────────────────────────

fn writeClEntry(w: *BitWriter, cl_enc: *const HuffEnc(19), e: ClEntry) !void {
	switch (e.kind) {
		.lit => try w.writeCode(cl_enc.code[e.val], cl_enc.len[e.val]),
		.rep16 => {
			try w.writeCode(cl_enc.code[16], cl_enc.len[16]);
			try w.writeBits(e.val - 3, 2);
		},
		.rep17 => {
			try w.writeCode(cl_enc.code[17], cl_enc.len[17]);
			try w.writeBits(e.val - 3, 3);
		},
		.rep18 => {
			try w.writeCode(cl_enc.code[18], cl_enc.len[18]);
			try w.writeBits(e.val - 11, 7);
		},
		.sep => {},
	}
}

pub fn writePadding(w: *BitWriter, padding: ?BitPadding) !void {
	const width: u3 = @intCast((8 - (w.totalBits() & 7)) & 7);
	const value: u8 = if (padding) |p| (if (p.width == width) p.value else 0) else 0;
	try w.writeBits(value, width);
}

pub fn finishDeflate(w: *BitWriter, block: Block) !void {
	const padding = if (block.is_last and block.body == .huff)
		(if (block.body.huff.encoding) |e| e.final_padding else null)
	else null;
	try writePadding(w, padding);
}

pub fn encodingHclen(h: Huff) usize {
	var n: usize = 19;
	while (n > 4 and h.cl_lengths[HCLEN_ORDER[n - 1]] == 0) n -= 1;
	if (h.encoding) |e| {
		if (n <= e.hclen and e.hclen <= 19) return e.hclen;
	}
	return n;
}

pub fn assembleBlock(w: *BitWriter, block: Block) !void {
	try w.writeBits(if (block.is_last) 1 else 0, 1);

	switch (block.body) {
		.stored => |data| {
			try w.writeBits(0, 2); // BTYPE 0
			try writePadding(w, block.alignment_padding);
			const n: u16 = @intCast(data.len);
			const nlen: u16 = n ^ 0xFFFF;
			const hdr = [4]u8{
				@intCast(n & 0xff),     @intCast(n >> 8),
				@intCast(nlen & 0xff),  @intCast(nlen >> 8),
			};
			try w.writeBytes(&hdr);
			try w.writeBytes(data);
			return;
		},
		.huff => |h| {
			var ll: HuffEnc(288) = undefined;
			var dist: HuffEnc(32) = undefined;

			if (h.is_fixed) {
				try w.writeBits(1, 2); // BTYPE 1
				ll = fixed_ll_enc;
				dist = fixed_dist_enc;
			} else {
				try w.writeBits(2, 2); // BTYPE 2

				const hclen = encodingHclen(h);

				try w.writeBits(@intCast(h.ll_lengths.len - 257), 5);
				try w.writeBits(@intCast(h.dist_lengths.len - 1), 5);
				try w.writeBits(@intCast(hclen - 4), 4);
				var i: usize = 0;
				while (i < hclen) : (i += 1) try w.writeBits(h.cl_lengths[HCLEN_ORDER[i]], 3);

				const cl_enc = HuffEnc(19).build(&h.cl_lengths) orelse return error.Malformed;
				for (h.cl_entries) |e| try writeClEntry(w, &cl_enc, e);

				ll = HuffEnc(288).build(h.ll_lengths) orelse return error.Malformed;
				dist = HuffEnc(32).build(h.dist_lengths) orelse return error.Malformed;
			}

			// Length 258: symbol 285 (0 extra) or 284+31 when 285 absent.
			const alt258 = ll.len[285] == 0;

			for (h.tokens) |tok| {
				switch (tok) {
					.lit => |b| {
						if (ll.len[b] == 0) return error.Malformed;
						try w.writeCode(ll.code[b], ll.len[b]);
					},
					.match => |m| {
						var ll_code: usize = undefined;
						var extra_n: u32 = undefined;
						var extra_v: u32 = undefined;
						if (m.length == 258 and (alt258 or (h.encoding != null and m.original_alt258 and ll.len[284] > 0))) {
							ll_code = 284;
							extra_n = 5;
							extra_v = 31;
						} else {
							const lc = lenCodeTable[m.length];
							ll_code = lc.code;
							extra_n = lc.extra;
							extra_v = m.length - LEN_BASE[lc.code - 257];
						}
						if (ll.len[ll_code] == 0) return error.Malformed;
						try w.writeCode(ll.code[ll_code], ll.len[ll_code]);
						try w.writeBits(extra_v, extra_n);

						const dc = distCodeTable[m.distance];
						if (dist.len[dc.code] == 0) return error.Malformed;
						try w.writeCode(dist.code[dc.code], dist.len[dc.code]);
						try w.writeBits(m.distance - DIST_BASE[dc.code], dc.extra);
					},
				}
			}
			if (ll.len[256] == 0) return error.Malformed;
			try w.writeCode(ll.code[256], ll.len[256]); // EOB
		},
	}
}

pub fn assembleDeflate(
	alloc: std.mem.Allocator,
	out: *std.ArrayList(u8),
	blocks: []const Block,
) !void {
	var w = BitWriter.init(out, alloc);
	for (blocks) |b| try assembleBlock(&w, b);
	if (blocks.len > 0) try finishDeflate(&w, blocks[blocks.len - 1]);
	try w.alignByte();
}

// ── gzip envelope ───────────────────────────────────────────────────────────

/// Length of the gzip header (bytes preceding the deflate stream), or null if
/// the header is malformed/truncated.
pub fn gzipHeaderLen(data: []const u8) ?usize {
	if (data.len < 18) return null;
	if (data[0] != 0x1f or data[1] != 0x8b or data[2] != 8) return null;
	const flg = data[3];
	var pos: usize = 10;
	if (flg & 0x04 != 0) {
		if (pos + 2 > data.len) return null;
		const xlen = @as(usize, data[pos]) | (@as(usize, data[pos + 1]) << 8);
		pos += 2 + xlen;
	}
	if (flg & 0x08 != 0) {
		while (pos < data.len and data[pos] != 0) pos += 1;
		pos += 1;
	}
	if (flg & 0x10 != 0) {
		while (pos < data.len and data[pos] != 0) pos += 1;
		pos += 1;
	}
	if (flg & 0x02 != 0) pos += 2;
	if (pos + 8 > data.len) return null;
	return pos;
}

/// True when a gzip member header carries the BGZF 'BC' FEXTRA subfield.
pub fn isBgzf(header: []const u8) bool {
	if (header.len < 12 or header[3] & 0x04 == 0) return false;
	const xlen = @as(usize, header[10]) | (@as(usize, header[11]) << 8);
	var p: usize = 12;
	const end = @min(12 + xlen, header.len);
	while (p + 4 <= end) {
		const slen = @as(usize, header[p + 2]) | (@as(usize, header[p + 3]) << 8);
		if (header[p] == 'B' and header[p + 1] == 'C' and slen == 2) return true;
		p += 4 + slen;
	}
	return false;
}

// ZIP structure uses the central directory as authoritative for sizes,
// including entries with data descriptors. Preserve fields as slices of
// the input. Rewriting changes only compressed sizes and affected offsets;
// CRC-32 and uncompressed sizes remain unchanged.

pub const ZIP_LFH_SIG = [4]u8{ 'P', 'K', 3, 4 }; // 0x04034b50 local file header
pub const ZIP_CDH_SIG = [4]u8{ 'P', 'K', 1, 2 }; // 0x02014b50 central directory header
pub const ZIP_EOCD_SIG = [4]u8{ 'P', 'K', 5, 6 }; // 0x06054b50 end of central directory
pub const ZIP_DD_SIG = [4]u8{ 'P', 'K', 7, 8 }; // 0x08074b50 data-descriptor signature
pub const ZIP_Z64_LOC_SIG = [4]u8{ 'P', 'K', 6, 7 }; // 0x07064b50 zip64 EOCD locator
pub const APK_SIG_BLOCK_MAGIC = "APK Sig Block 42"; // 16 bytes preceding the CD

pub const ZIP_FLAG_ENCRYPTED: u16 = 0x0001; // GP flag bit 0
pub const ZIP_FLAG_DATA_DESC: u16 = 0x0008; // GP flag bit 3
pub const ZIP_METHOD_DEFLATE: u16 = 8;

fn rdU16le(d: []const u8, p: usize) u16 {
	return @as(u16, d[p]) | (@as(u16, d[p + 1]) << 8);
}

fn rdU32le(d: []const u8, p: usize) u32 {
	return @as(u32, d[p]) | (@as(u32, d[p + 1]) << 8) |
		(@as(u32, d[p + 2]) << 16) | (@as(u32, d[p + 3]) << 24);
}

fn wrU32le(buf: []u8, p: usize, v: u32) void {
	buf[p] = @intCast(v & 0xff);
	buf[p + 1] = @intCast((v >> 8) & 0xff);
	buf[p + 2] = @intCast((v >> 16) & 0xff);
	buf[p + 3] = @intCast((v >> 24) & 0xff);
}

pub const ZipEntry = struct {
	lfh: []const u8, // local file header: 30-byte fixed + name + extra, verbatim
	data: []const u8, // compressed bytes (comp_size long), verbatim
	descriptor: []const u8, // data-descriptor bytes ("" when GP bit 3 clear), verbatim
	pad: []const u8, // bytes between this entry's end and the next local header
	cdh: []const u8, // central directory record, verbatim
	method: u16,
	gp_flag: u16,
	crc32: u32,
	comp_size: u32, // from the CD (authoritative)
	uncomp_size: u32,
	local_offset: u32, // CD's stored relative-offset field (pre-bias)
	orig_lh_pos: usize, // actual file position of this local header
	// Optimizer scratch (set by deflopt.zig optimizeZip before assembly):
	new_data: []const u8 = &.{}, // replacement compressed bytes; "" → reuse .data
	reoptimized: bool = false,

	pub fn outData(self: ZipEntry) []const u8 {
		return if (self.reoptimized) self.new_data else self.data;
	}
};

pub const ZipArchive = struct {
	prefix: []const u8, // bytes before the first local header (SFX stub, etc.)
	entries: []ZipEntry, // in CENTRAL-DIRECTORY order
	eocd: []const u8, // end-of-central-directory record + comment, verbatim
	prefix_bias: i64, // actual_cd_start - EOCD's cd_offset field
	passthrough: bool = false, // zip64 / APK-sig-block: whole file emitted unchanged
	raw: []const u8 = &.{}, // original bytes, kept for passthrough emission
	reason: []const u8 = "", // why passthrough (diagnostic)
};

/// Offset of the End Of Central Directory record, or null. Enforces the
/// trailing-garbage contract: the EOCD comment must extend EXACTLY to EOF
/// (bytes after the archive are never silently dropped).
fn zipFindEocd(data: []const u8) ?usize {
	if (data.len < 22) return null;
	// Comment ≤ 65535; scan back far enough to clear the largest legal comment.
	const lo: usize = if (data.len > 22 + 0xFFFF) data.len - 22 - 0xFFFF else 0;
	var idx: usize = data.len - 22; // highest start where a full EOCD record fits
	while (true) {
		if (std.mem.eql(u8, data[idx .. idx + 4], &ZIP_EOCD_SIG)) {
			const comment_len: usize = rdU16le(data, idx + 20);
			if (idx + 22 + comment_len == data.len) return idx;
		}
		if (idx == lo) return null;
		idx -= 1;
	}
}

/// True if a local/central extra field carries a Zip64 Extended Information
/// block (header ID 0x0001) — the authoritative per-entry zip64 marker even
/// when totals fit in 32 bits (force_zip64).
fn zipExtraHasZip64(extra: []const u8) bool {
	var p: usize = 0;
	while (p + 4 <= extra.len) {
		const hid = rdU16le(extra, p);
		const size = rdU16le(extra, p + 2);
		if (hid == 0x0001) return true;
		p += 4 + @as(usize, size);
	}
	return false;
}

/// Cheap dispatch predicate: a local-header/EOCD/CD signature at the front, or a
/// locatable EOCD (covers SFX-prefixed archives).
pub fn looksLikeZip(data: []const u8) bool {
	if (data.len >= 4) {
		const h = data[0..4];
		if (std.mem.eql(u8, h, &ZIP_LFH_SIG) or std.mem.eql(u8, h, &ZIP_EOCD_SIG) or
			std.mem.eql(u8, h, &ZIP_CDH_SIG)) return true;
	}
	return zipFindEocd(data) != null;
}

fn passthroughArchive(data: []const u8, eocd: []const u8, reason: []const u8) ZipArchive {
	return .{ .prefix = &.{}, .entries = &.{}, .eocd = eocd, .prefix_bias = 0, .passthrough = true, .raw = data, .reason = reason };
}

/// Walk a ZIP container via its central directory. error.Malformed on multi-disk
/// archives and on trailing garbage. Zip64 / APK-signing-block containers are
/// DETECTED and returned with passthrough=true (whole-file byte-exact emission).
pub fn parseZipMembers(alloc: std.mem.Allocator, data: []const u8) ParseError!ZipArchive {
	const eocd_pos = zipFindEocd(data) orelse return error.Malformed;

	const disk_no = rdU16le(data, eocd_pos + 4);
	const cd_disk = rdU16le(data, eocd_pos + 6);
	const cd_count_disk = rdU16le(data, eocd_pos + 8);
	const total_entries = rdU16le(data, eocd_pos + 10);
	const cd_size = rdU32le(data, eocd_pos + 12);
	const cd_offset = rdU32le(data, eocd_pos + 16);

	if (disk_no != 0 or cd_disk != 0) return error.Malformed; // multi-disk

	const eocd = data[eocd_pos..];

	// Zip64 detection: a zip64 EOCD locator immediately precedes the EOCD, or a
	// sentinel sits in a count/size/offset field.
	var zip64 = (eocd_pos >= 20 and std.mem.eql(u8, data[eocd_pos - 20 .. eocd_pos - 16], &ZIP_Z64_LOC_SIG));
	if (total_entries == 0xFFFF or cd_count_disk == 0xFFFF or cd_size == 0xFFFFFFFF or cd_offset == 0xFFFFFFFF) zip64 = true;
	if (zip64) return passthroughArchive(data, eocd, "zip64");

	if (cd_size > eocd_pos) return error.Malformed; // CD size overruns file start
	const actual_cd_start = eocd_pos - cd_size;

	// APK v2/v3 signing block sits between the last entry and the CD, ending in a
	// 16-byte magic immediately before the CD. Any rewrite bricks the signature.
	if (actual_cd_start >= 16 and std.mem.eql(u8, data[actual_cd_start - 16 .. actual_cd_start], APK_SIG_BLOCK_MAGIC))
		return passthroughArchive(data, eocd, "apk-sig-block");

	const prefix_bias: i64 = @as(i64, @intCast(actual_cd_start)) - @as(i64, cd_offset);

	// ---- pass 1: walk the central directory (authoritative) ----
	var entries: std.ArrayList(ZipEntry) = .empty;
	var p: usize = actual_cd_start;
	var i: usize = 0;
	while (i < total_entries) : (i += 1) {
		if (p + 46 > data.len or !std.mem.eql(u8, data[p .. p + 4], &ZIP_CDH_SIG)) return error.Malformed;
		const gp = rdU16le(data, p + 8);
		const method = rdU16le(data, p + 10);
		const crc = rdU32le(data, p + 16);
		const comp = rdU32le(data, p + 20);
		const uncomp = rdU32le(data, p + 24);
		const n: usize = rdU16le(data, p + 28);
		const m: usize = rdU16le(data, p + 30);
		const k: usize = rdU16le(data, p + 32);
		const disk_start = rdU16le(data, p + 34);
		const local_off = rdU32le(data, p + 42);
		if (disk_start != 0 and disk_start != 0xFFFF) return error.Malformed; // multi-disk
		const cdh_len = 46 + n + m + k;
		if (p + cdh_len > data.len) return error.Malformed; // truncated CD record
		const cdh = data[p .. p + cdh_len];
		const cd_extra = cdh[46 + n .. 46 + n + m];
		if (comp == 0xFFFFFFFF or uncomp == 0xFFFFFFFF or local_off == 0xFFFFFFFF or zipExtraHasZip64(cd_extra))
			return passthroughArchive(data, eocd, "zip64-entry");
		try entries.append(alloc, .{
			.lfh = &.{}, .data = &.{}, .descriptor = &.{}, .pad = &.{}, .cdh = cdh,
			.method = method, .gp_flag = gp, .crc32 = crc, .comp_size = comp,
			.uncomp_size = uncomp, .local_offset = local_off, .orig_lh_pos = 0,
		});
		p += cdh_len;
	}
	if (p != eocd_pos) return error.Malformed; // CD ends short of / past the EOCD

	// ---- pass 2: locate + capture each local entry ----
	for (entries.items) |*e| {
		const lh_pos_i = @as(i64, e.local_offset) + prefix_bias;
		if (lh_pos_i < 0 or lh_pos_i + 30 > @as(i64, @intCast(data.len))) return error.Malformed;
		const lh_pos: usize = @intCast(lh_pos_i);
		if (!std.mem.eql(u8, data[lh_pos .. lh_pos + 4], &ZIP_LFH_SIG)) return error.Malformed;
		const ln: usize = rdU16le(data, lh_pos + 26);
		const lm: usize = rdU16le(data, lh_pos + 28);
		const lfh_len = 30 + ln + lm;
		if (lh_pos + lfh_len > data.len) return error.Malformed;
		const lfh = data[lh_pos .. lh_pos + lfh_len];
		if (zipExtraHasZip64(lfh[30 + ln .. 30 + ln + lm]))
			return passthroughArchive(data, eocd, "zip64-entry");
		// Reject inconsistent local/central CRC and size fields. With a data
		// descriptor, local fields must be all-zero or exactly match the central
		// directory; do not silently normalize inconsistent input.
		const lfh_crc = rdU32le(data, lh_pos + 14);
		const lfh_comp = rdU32le(data, lh_pos + 18);
		const lfh_uncomp = rdU32le(data, lh_pos + 22);
		const cd_match = lfh_crc == e.crc32 and lfh_comp == e.comp_size and
			lfh_uncomp == e.uncomp_size;
		if (e.gp_flag & ZIP_FLAG_DATA_DESC != 0) {
			const zeros = lfh_crc == 0 and lfh_comp == 0 and lfh_uncomp == 0;
			if (!zeros and !cd_match) return error.Malformed;
		} else if (!cd_match) return error.Malformed;
		const data_start = lh_pos + lfh_len;
		if (data_start + e.comp_size > data.len) return error.Malformed; // truncated data
		const comp_data = data[data_start .. data_start + e.comp_size];
		const dd_start = data_start + e.comp_size;
		var descriptor: []const u8 = &.{};
		if (e.gp_flag & ZIP_FLAG_DATA_DESC != 0) {
			// Optional 4-byte signature, then crc/comp/uncomp (4 each). Disambiguate
			// by the signature; validate ALL THREE fields against the CD (same
			// mismatch = hard-error ruling as the LFH above).
			const has_sig = dd_start + 4 <= data.len and std.mem.eql(u8, data[dd_start .. dd_start + 4], &ZIP_DD_SIG);
			const dlen: usize = if (has_sig) 16 else 12;
			if (dd_start + dlen > data.len) return error.Malformed; // truncated descriptor
			descriptor = data[dd_start .. dd_start + dlen];
			const base: usize = if (has_sig) 4 else 0;
			if (rdU32le(descriptor, base) != e.crc32 or
				rdU32le(descriptor, base + 4) != e.comp_size or
				rdU32le(descriptor, base + 8) != e.uncomp_size) return error.Malformed;
		}
		e.lfh = lfh;
		e.data = comp_data;
		e.descriptor = descriptor;
		e.orig_lh_pos = lh_pos;
	}

	// ---- pass 3: capture inter-entry padding (verbatim gaps, physical order) ----
	const phys = try alloc.alloc(usize, entries.items.len);
	for (phys, 0..) |*x, idx| x.* = idx;
	std.sort.block(usize, phys, entries.items, struct {
		fn lt(items: []const ZipEntry, x: usize, y: usize) bool {
			return items[x].orig_lh_pos < items[y].orig_lh_pos;
		}
	}.lt);
	const first_lh_pos = if (entries.items.len > 0) entries.items[phys[0]].orig_lh_pos else actual_cd_start;
	for (phys, 0..) |j, rank| {
		const e = &entries.items[j];
		const end = e.orig_lh_pos + e.lfh.len + e.data.len + e.descriptor.len;
		const nxt = if (rank + 1 < phys.len) entries.items[phys[rank + 1]].orig_lh_pos else actual_cd_start;
		if (end > nxt) return error.Malformed; // entry overlaps next local header
		e.pad = data[end..nxt];
	}

	return .{
		.prefix = data[0..first_lh_pos],
		.entries = entries.items,
		.eocd = eocd,
		.prefix_bias = prefix_bias,
	};
}

/// Inverse of parseZipMembers: rebuild from verbatim blobs, surgically rewriting
/// only the compressed-size fields and local-header offsets. For an unmodified
/// archive this is byte-exact.
pub fn assembleZipMembers(alloc: std.mem.Allocator, arc: ZipArchive) ![]u8 {
	if (arc.passthrough) {
		const out = try alloc.alloc(u8, arc.raw.len);
		@memcpy(out, arc.raw);
		return out;
	}

	var out: std.ArrayList(u8) = .empty;
	try out.appendSlice(alloc, arc.prefix);

	// Data section in PHYSICAL (original local-header) order.
	const phys = try alloc.alloc(usize, arc.entries.len);
	for (phys, 0..) |*x, idx| x.* = idx;
	std.sort.block(usize, phys, arc.entries, struct {
		fn lt(items: []const ZipEntry, x: usize, y: usize) bool {
			return items[x].orig_lh_pos < items[y].orig_lh_pos;
		}
	}.lt);

	const new_lh_pos = try alloc.alloc(usize, arc.entries.len); // keyed by CD index
	for (phys) |j| {
		const e = arc.entries[j];
		new_lh_pos[j] = out.items.len;
		const payload = e.outData();
		const lfh = try alloc.dupe(u8, e.lfh);
		// Rewrite the LFH compressed size when it carries one: always without a
		// descriptor; with one, only for the mirrored-sizes writer pattern
		// (parse validated the mirror, a re-encode must keep it honest) —
		// spec-zeroed fields stay zero.
		if (e.gp_flag & ZIP_FLAG_DATA_DESC == 0 or rdU32le(lfh, 18) != 0)
			wrU32le(lfh, 18, @intCast(payload.len));
		try out.appendSlice(alloc, lfh);
		try out.appendSlice(alloc, payload);
		if (e.descriptor.len > 0) {
			const desc = try alloc.dupe(u8, e.descriptor);
			const has_sig = std.mem.eql(u8, desc[0..4], &ZIP_DD_SIG);
			wrU32le(desc, if (has_sig) 8 else 4, @intCast(payload.len));
			try out.appendSlice(alloc, desc);
		}
		try out.appendSlice(alloc, e.pad);
	}

	const new_cd_start = out.items.len;
	for (arc.entries, 0..) |e, j| { // CD order preserved
		const cdh = try alloc.dupe(u8, e.cdh);
		wrU32le(cdh, 20, @intCast(e.outData().len));
		wrU32le(cdh, 42, @intCast(@as(i64, @intCast(new_lh_pos[j])) - arc.prefix_bias));
		try out.appendSlice(alloc, cdh);
	}
	const new_cd_size = out.items.len - new_cd_start;

	const eocd = try alloc.dupe(u8, arc.eocd);
	wrU32le(eocd, 12, @intCast(new_cd_size));
	wrU32le(eocd, 16, @intCast(@as(i64, @intCast(new_cd_start)) - arc.prefix_bias));
	try out.appendSlice(alloc, eocd);
	return out.items;
}

test "assembly rejects absent literal, distance, and EOB codes" {
	var ll = [_]u8{0} ** 258;
	var dist = [_]u8{0};
	var tokens = [_]Token{.{ .lit = 65 }};
	const cases = [_]u8{ 0, 1, 2 };
	for (cases) |case| {
		@memset(&ll, 0);
		ll[256] = 1;
		tokens[0] = .{ .lit = 65 };
		if (case == 1) {
			ll[257] = 1;
			tokens[0] = .{ .match = .{ .length = 3, .distance = 1 } };
		} else if (case == 2) {
			ll[256] = 0;
			ll[65] = 1;
		}
		// Header contents are immaterial to these encoder invariant checks.
		const block = Block{ .is_last = true, .body = .{ .huff = .{
			.is_fixed = false,
			.tokens = if (case == 2) tokens[0..0] else &tokens,
			.ll_lengths = &ll,
			.dist_lengths = &dist,
			.cl_lengths = [_]u8{0} ** 19,
			.cl_entries = &.{},
		} } };
		var out: std.ArrayList(u8) = .empty;
		defer out.deinit(std.testing.allocator);
		var w = BitWriter.init(&out, std.testing.allocator);
		try std.testing.expectError(error.Malformed, assembleBlock(&w, block));
	}
}
