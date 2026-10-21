//! Raw DEFLATE measurement, without decompression or checksum validation.

const std = @import("std");
const common = @import("deflcommon.zig");

const BitReader = common.BitReader;
const HuffDec = common.HuffDec;
const parseClLengths = common.parseClLengths;
const LEN_EXTRA = common.LEN_EXTRA;
const DIST_EXTRA = common.DIST_EXTRA;
const HCLEN_ORDER = common.HCLEN_ORDER;
const ERR = common.ERR;
const MAX_SYMS = common.MAX_SYMS;

// ── Legality class ──────────────────────────────────────
//
// Strictest class every dynamic block of the walked stream satisfies, as a
// side channel of the count:
//   complete    lit/len, distance and CL codes all complete (Kraft sum 1)
//   zlib        what zlib 1.3.2 inflates: complete CL code; lit/len and
//                distance complete, or one 1-bit code, or (distance) none
//   decodable   any prefix codes with Kraft sum <= 1
// Stored and fixed blocks constrain nothing. Callers reset before a new file.
pub const Legality = enum(i32) { complete = 0, zlib = 1, decodable = 2 };
pub threadlocal var worst_class: Legality = .complete;

/// Actual stream statistics, distinct from the historical normalized counter.
/// Measurement does not validate payload checksums or expand matches.
pub const Statistics = extern struct {
	bits: u64 = 0,
	blocks: u64 = 0,
	streams: u64 = 0,
	opaque_streams: u64 = 0,
	legality: Legality = .complete,
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

fn noteBlockClass(ll: []const u8, dist: []const u8, cl: []const u8) void {
	for ([_]Legality{ codeClass(ll, 15, false), codeClass(dist, 15, true), codeClass(cl, 7, false) }) |class| {
		if (@intFromEnum(class) > @intFromEnum(worst_class)) worst_class = class;
	}
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

/// Count normalized DEFLATE bits of a raw deflate stream (no envelope).
/// Returns -1 on parse failure.
pub fn count(data: []const u8, stats: ?*Statistics) i64 {
	var r = BitReader{ .data = data };
	const bits = countReader(&r, stats);
	if (stats != null and (r.pos() + 7) / 8 != data.len) return ERR;
	return bits;
}

/// Count from a caller-owned reader, leaving it at the stream's end so
/// container counters can locate the trailer and subsequent streams.
pub fn countReader(r: *BitReader, stats: ?*Statistics) i64 {
	var total: i64 = 0;
	var blocks: u64 = 0;
	const start = r.pos();

	while (true) {
		// A new block must begin within the data.
		if (r.atEnd()) return ERR;
		const before = r.pos();
		const bfinal = r.read(1);
		const btype: common.BlockType = @enumFromInt(r.read(2));

		if (btype == .stored) {
			// Stored: byte-align, LEN(16), NLEN(16), then LEN data bytes.
			// LEN/NLEN must come from real bytes.
			r.byteAlign();
			if (r.realAvail() < 4) return ERR;
			const len_lo = r.read(8);
			const len_hi = r.read(8);
			const nlen_lo = r.read(8);
			const nlen_hi = r.read(8);
			const slen: usize = @intCast(len_lo | (len_hi << 8));
			if ((nlen_lo | (nlen_hi << 8)) != slen ^ 0xFFFF) return ERR;
			if (!r.skipBytes(slen)) return ERR; // truncated
			// Normalized stored accounting: real cost is 35..42+8*len,
			// depending on stream alignment. Statistics retain the actual cost.
			total += 40 + 8 * @as(i64, @intCast(slen));
		} else if (btype == .fixed) {
			if (!walkTokens(r, &common.fixed_ll_dec, &common.fixed_dist_dec)) return ERR;
			total += @intCast(r.pos() - before);
		} else if (btype == .dynamic) {
			const hlit = r.read(5) + common.FIRST_LENGTH_SYMBOL;
			const hdist = r.read(5) + 1;
			const hclen = r.read(4) + 4;
			if (hlit > 286) return ERR;

			var cl_lengths = [_]u8{0} ** 19;
			var i: usize = 0;
			while (i < hclen) : (i += 1) {
				cl_lengths[HCLEN_ORDER[i]] = @intCast(r.read(3));
			}
			const cl = HuffDec.build(&cl_lengths) orelse return ERR;

			// RFC 1951 §3.2.7: lit/len and distance code lengths form ONE shared
			// run-length sequence of hlit+hdist values. A repeat code (16/17/18)
			// may straddle the hlit boundary, so decode the whole sequence in a
			// single pass — decoding hlit then hdist separately would reject a
			// legal crossing repeat (overshoot guard) and fail valid streams.
			var combined = [_]u8{0} ** (MAX_SYMS + 32);
			if (!parseClLengths(r, &cl, combined[0 .. hlit + hdist])) return ERR;

			const ll = HuffDec.build(combined[0..hlit]) orelse return ERR;
			const dist = HuffDec.build(combined[hlit .. hlit + hdist]) orelse return ERR;
			noteBlockClass(combined[0..hlit], combined[hlit .. hlit + hdist], &cl_lengths);
			if (!walkTokens(r, &ll, &dist)) return ERR;
			total += @intCast(r.pos() - before);
		} else {
			return ERR; // reserved BTYPE 3
		}

		// Lookahead may zero-fill, but even a final EOB must consume real bits.
		if (r.pos() > r.data.len * 8) return ERR;
		blocks += 1;
		if (bfinal == 1) break;
	}
	if (stats) |s| {
		s.bits += r.pos() - start;
		s.blocks += blocks;
		s.streams += 1;
		s.legality = worst_class;
	}
	return total;
}

