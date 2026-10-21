//! DEFLATE parser and assembler. Blocks retain tokens, Huffman lengths,
//! CL RLE entries and original spelling details for bit-exact roundtrips.

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

// Comptime-built fixed-table encoders (assemble side; the decode side uses
// common.fixed_ll_dec / common.fixed_dist_dec) — no per-block rebuilds.
const fixed_ll_enc = HuffEnc(288).build(&common.fixed_ll_lengths).?;
const fixed_dist_enc = HuffEnc(32).build(&common.fixed_dist_lengths).?;

// ── parsing ─────────────────────────────────────────────────────────────────

/// Fill out with CL code lengths, appending the exact RLE entries.
fn parseClSeq(
	r: *BitReader,
	cl: *const HuffDec,
	out: []u8,
	entries: *std.ArrayList(ClEntry),
	alloc: std.mem.Allocator,
) ParseError!void {
	var i: usize = 0;
	while (i < out.len) {
		const sym = cl.decode(r) orelse return error.Malformed;
		if (sym <= 15) {
			out[i] = @intCast(sym);
			i += 1;
			try entries.append(alloc, .{ .kind = .lit, .val = sym });
		} else {
			if (sym == 16 and i == 0) return error.Malformed;
			const count = switch (sym) {
				16 => r.read(2) + 3,
				17 => r.read(3) + 3,
				18 => r.read(7) + 11,
				else => return error.Malformed,
			};
			if (count > out.len - i) return error.Malformed;
			@memset(out[i..][0..count], if (sym == 16) out[i - 1] else 0);
			i += count;
			try entries.append(alloc, .{
				.kind = switch (sym) { 16 => .rep16, 17 => .rep17, 18 => .rep18, else => unreachable },
				.val = @intCast(count),
			});
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
		if (sym < common.EOB) {
			try tokens.append(alloc, .{ .lit = @intCast(sym) });
			continue;
		}
		if (sym == common.EOB) return;
		if (sym > 285) return error.Malformed;
		const mlen: u16 = @intCast(LEN_BASE[sym - common.FIRST_LENGTH_SYMBOL] + r.read(LEN_EXTRA[sym - common.FIRST_LENGTH_SYMBOL]));
		const dsym = dist.decode(r) orelse return error.Malformed;
		if (dsym > 29) return error.Malformed;
		const mdist: u16 = @intCast(DIST_BASE[dsym] + r.read(DIST_EXTRA[dsym]));
		try tokens.append(alloc, .{ .match = .{
			.length = mlen, .distance = mdist, .original_alt258 = sym == 284 and mlen == common.MAX_MATCH_LENGTH,
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
	const btype: common.BlockType = @enumFromInt(r.read(2));

	if (btype == .stored) {
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

	if (btype == .fixed) {
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

	if (btype == .dynamic) {
		const hlit = r.read(5) + common.FIRST_LENGTH_SYMBOL;
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
		try parseClSeq(r, &cl, combined, &entries, alloc);
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
			try w.writeBits(@intFromEnum(common.BlockType.stored), 2);
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
				try w.writeBits(@intFromEnum(common.BlockType.fixed), 2);
				ll = fixed_ll_enc;
				dist = fixed_dist_enc;
			} else {
				try w.writeBits(@intFromEnum(common.BlockType.dynamic), 2);

				const hclen = encodingHclen(h);

				try w.writeBits(@intCast(h.ll_lengths.len - common.FIRST_LENGTH_SYMBOL), 5);
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
						if (m.length == common.MAX_MATCH_LENGTH and (alt258 or (h.encoding != null and m.original_alt258 and ll.len[284] > 0))) {
							ll_code = 284;
							extra_n = 5;
							extra_v = 31;
						} else {
							const lc = lenCodeTable[m.length];
							ll_code = lc.code;
							extra_n = lc.extra;
							extra_v = m.length - LEN_BASE[lc.code - common.FIRST_LENGTH_SYMBOL];
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
			if (ll.len[common.EOB] == 0) return error.Malformed;
			try w.writeCode(ll.code[common.EOB], ll.len[common.EOB]);
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

test "assembly rejects absent literal, distance, and EOB codes" {
	var ll = [_]u8{0} ** (common.FIRST_LENGTH_SYMBOL + 1);
	var dist = [_]u8{0};
	var tokens = [_]Token{.{ .lit = 65 }};
	const cases = [_]u8{ 0, 1, 2 };
	for (cases) |case| {
		@memset(&ll, 0);
		ll[common.EOB] = 1;
		tokens[0] = .{ .lit = 65 };
		if (case == 1) {
			ll[common.FIRST_LENGTH_SYMBOL] = 1;
			tokens[0] = .{ .match = .{ .length = 3, .distance = 1 } };
		} else if (case == 2) {
			ll[common.EOB] = 0;
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
