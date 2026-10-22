//! Raw DEFLATE measurement, without decompression or checksum validation.

const std = @import("std");
const common = @import("deflcommon.zig");

const BitReader = common.BitReader;
const HuffDec = common.HuffDec;
const parseClLengths = common.parseClLengths;
const LEN_EXTRA = common.LEN_EXTRA;
const DIST_EXTRA = common.DIST_EXTRA;
const HCLEN_ORDER = common.HCLEN_ORDER;
const MAX_SYMS = common.MAX_SYMS;

// ── Legality class ──────────────────────────────────────
//
// Strictest class every dynamic block of the walked stream satisfies:
//   complete    lit/len, distance and CL codes all complete (Kraft sum 1)
//   zlib        what zlib 1.3.2 inflates: complete CL code; lit/len and
//                distance complete, or one 1-bit code, or (distance) none
//   decodable   any prefix codes with Kraft sum <= 1
// Stored and fixed blocks constrain nothing.
pub const Legality = enum(i32) { complete = 0, zlib = 1, decodable = 2 };

/// Stream statistics; failed streams never contribute partial results.
/// Measurement does not validate payload checksums or expand matches.
pub const Statistics = extern struct {
	bits: u64 = 0,
	blocks: u64 = 0,
	streams: u64 = 0,
	opaque_streams: u64 = 0,
	legality: Legality = .complete,

	pub fn add(self: *Statistics, other: Statistics) void {
		self.bits += other.bits;
		self.blocks += other.blocks;
		self.streams += other.streams;
		self.opaque_streams += other.opaque_streams;
		self.legality = @enumFromInt(@max(@intFromEnum(self.legality), @intFromEnum(other.legality)));
	}
};

fn codeClass(lengths: []const u8, max_len: u6, allow_empty: bool) Legality {
	var kraft: u64 = 0;
	var ncodes: usize = 0;
	var longest: u8 = 0;
	for (lengths) |l| {
		if (l == 0) continue;
		kraft += @as(u64, 1) << @intCast(max_len - l);
		ncodes += 1;
		longest = @max(longest, l);
	}
	if (kraft == (@as(u64, 1) << max_len)) return .complete;
	if (ncodes == 0) return if (allow_empty) .zlib else .decodable;
	if (ncodes == 1 and longest == 1) return .zlib;
	return .decodable;
}

fn blockClass(ll: []const u8, dist: []const u8, cl: []const u8) Legality {
	var worst: Legality = .complete;
	for ([_]Legality{ codeClass(ll, 15, false), codeClass(dist, 15, true), codeClass(cl, 7, false) }) |class| {
		if (@intFromEnum(class) > @intFromEnum(worst)) worst = class;
	}
	return worst;
}

// ── DEFLATE stream bit counter ──────────────────────────────────────────────

/// Walk the token stream of a Huffman block to (and including) EOB. Advances
/// the reader; the caller derives bit cost from the cursor delta. Returns false
/// on any decode error.
fn walkTokens(r: *BitReader, ll: *const HuffDec, dist: *const HuffDec) bool {
	while (true) {
		if (r.atEnd()) return false; // would decode a symbol past end → truncated
		const sym = ll.decode(r) orelse return false;
		if (sym < common.EOB) continue; // literal
		if (sym == common.EOB) return true;
		if (sym > 285) return false; // invalid length symbol
		// length extra bits
		_ = r.read(LEN_EXTRA[sym - common.FIRST_LENGTH_SYMBOL]);
		// distance symbol + extra bits
		const dsym = dist.decode(r) orelse return false;
		if (dsym > 29) return false;
		_ = r.read(DIST_EXTRA[dsym]);
	}
}

/// Require exactly one stream, ending in the final input byte.
pub fn count(data: []const u8) error{Malformed}!Statistics {
	const result = try scan(data);
	if ((result.bits + 7) / 8 != data.len) return error.Malformed;
	return result;
}

/// Measure the first stream. Its consumed byte extent is ceil(bits / 8).
/// No payload expansion, checksum verification or allocation.
pub fn scan(data: []const u8) error{Malformed}!Statistics {
	var reader = BitReader{ .data = data };
	const r = &reader;
	var blocks: u64 = 0;
	var legality: Legality = .complete;

	while (true) {
		// A new block must begin within the data.
		if (r.atEnd()) return error.Malformed;
		const bfinal = r.read(1);
		const btype: common.BlockType = @enumFromInt(r.read(2));

		if (btype == .stored) {
			// Stored: byte-align, LEN(16), NLEN(16), then LEN data bytes.
			// LEN/NLEN must come from real bytes.
			r.byteAlign();
			if (r.realAvail() < 4) return error.Malformed;
			const slen = r.read(16);
			if (r.read(16) != slen ^ 0xFFFF) return error.Malformed;
			if (!r.skipBytes(slen)) return error.Malformed; // truncated
		} else if (btype == .fixed) {
			if (!walkTokens(r, &common.fixed_ll_dec, &common.fixed_dist_dec)) return error.Malformed;
		} else if (btype == .dynamic) {
			const hlit = r.read(5) + common.FIRST_LENGTH_SYMBOL;
			const hdist = r.read(5) + 1;
			const hclen = r.read(4) + 4;
			if (hlit > 286) return error.Malformed;

			var cl_lengths = [_]u8{0} ** 19;
			var i: usize = 0;
			while (i < hclen) : (i += 1) {
				cl_lengths[HCLEN_ORDER[i]] = @intCast(r.read(3));
			}
			const cl = HuffDec.build(&cl_lengths) orelse return error.Malformed;

			// RFC 1951 §3.2.7: lit/len and distance code lengths form ONE shared
			// run-length sequence of hlit+hdist values. A repeat code (16/17/18)
			// may straddle the hlit boundary, so decode the whole sequence in a
			// single pass — decoding hlit then hdist separately would reject a
			// legal crossing repeat (overshoot guard) and fail valid streams.
			var combined = [_]u8{0} ** (MAX_SYMS + 32);
			if (!parseClLengths(r, &cl, combined[0 .. hlit + hdist])) return error.Malformed;

			const ll = HuffDec.build(combined[0..hlit]) orelse return error.Malformed;
			const dist = HuffDec.build(combined[hlit .. hlit + hdist]) orelse return error.Malformed;
			const class = blockClass(combined[0..hlit], combined[hlit .. hlit + hdist], &cl_lengths);
			if (@intFromEnum(class) > @intFromEnum(legality)) legality = class;
			if (!walkTokens(r, &ll, &dist)) return error.Malformed;
		} else {
			return error.Malformed; // reserved BTYPE 3
		}

		// Lookahead may zero-fill, but even a final EOB must consume real bits.
		if (r.pos() > r.data.len * 8) return error.Malformed;
		blocks += 1;
		if (bfinal == 1) break;
	}
	return .{ .bits = r.pos(), .blocks = blocks, .streams = 1, .legality = legality };
}

test "measurement results isolate legality and count actual alignment" {
	const dynamic = [_]u8{ 0x05, 0xc0, 0x81, 0, 0, 0, 0, 0, 0x90, 0xff, 0x6b, 0 };
	const prior = try scan(&dynamic);
	try std.testing.expectEqual(Legality.zlib, prior.legality);
	try std.testing.expectError(error.Malformed, scan(dynamic[0 .. dynamic.len - 1]));
	// A fixed empty block followed by a stored empty block: 48 bits including alignment.
	const stored = [_]u8{ 2, 4, 0, 0, 0xff, 0xff };
	const result = try count(&stored);
	try std.testing.expectEqualDeep(Statistics{ .bits = 48, .blocks = 2, .streams = 1 }, result);
	const suffixed = stored ++ "suffix";
	try std.testing.expectEqualDeep(result, try scan(suffixed));
	try std.testing.expectError(error.Malformed, count(suffixed));
}

