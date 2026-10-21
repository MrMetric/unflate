//! Gzip members, header integrity and BGZF preservation.

const std = @import("std");
const deflate = @import("deflopt.zig");
const byteio = @import("byteio.zig");
const rdint_le = byteio.rdint_le;

const CM_DEFLATE = 8;
const FHCRC: u8 = 0x02;
const FEXTRA: u8 = 0x04;
const FNAME: u8 = 0x08;
const FCOMMENT: u8 = 0x10;
const RESERVED_FLAGS: u8 = 0xe0;

/// Length of the gzip header (bytes preceding the deflate stream), or null if
/// the header is malformed/truncated.
pub fn headerLen(data: []const u8) ?usize {
	return parseHeader(data, true);
}

fn parseHeader(data: []const u8, integrity: bool) ?usize {
	if (data.len < 18) return null;
	if (data[0] != 0x1f or data[1] != 0x8b or data[2] != CM_DEFLATE) return null;
	const flg = data[3];
	if (integrity and flg & RESERVED_FLAGS != 0) return null;
	var pos: usize = 10;
	if (flg & FEXTRA != 0) {
		if (pos + 2 > data.len) return null;
		const xlen: usize = rdint_le(u16, data, pos);
		pos += 2 + xlen;
	}
	for ([_]u8{ FNAME, FCOMMENT }) |flag| {
		if (flg & flag != 0) {
			while (pos < data.len and data[pos] != 0) pos += 1;
			pos += 1;
		}
	}
	if (flg & FHCRC != 0) {
		if (pos + 2 > data.len) return null;
		const expected = rdint_le(u16, data, pos);
		if (integrity and @as(u16, @truncate(std.hash.crc.Crc32.hash(data[0..pos]))) != expected) return null;
		pos += 2;
	}
	if (pos + 8 > data.len) return null;
	return pos;
}

/// True when a gzip member header carries the BGZF 'BC' FEXTRA subfield.
pub fn isBgzf(header: []const u8) bool {
	if (header.len < 12 or header[3] & FEXTRA == 0) return false;
	const xlen: usize = rdint_le(u16, header, 10);
	var p: usize = 12;
	const end = @min(12 + xlen, header.len);
	while (p + 4 <= end) {
		const slen: usize = rdint_le(u16, header, p + 2);
		if (header[p] == 'B' and header[p + 1] == 'C' and slen == 2) return true;
		p += 4 + slen;
	}
	return false;
}


/// Optimize concatenated members, preserving headers and trailers verbatim.
/// BGZF offsets require the whole file to remain unchanged after validation.
pub fn optimize(a: std.mem.Allocator, in: []const u8, options: deflate.Options, allow_growth: bool) ![]const u8 {
	var out: std.ArrayList(u8) = .empty;
	try out.ensureTotalCapacity(a, in.len);
	var pos: usize = 0;
	var preserve = false;
	if (in.len == 0) return error.Malformed;
	while (pos < in.len) {
		const rem = in[pos..];
		const hlen = headerLen(rem) orelse return error.Malformed;
		preserve = preserve or isBgzf(rem[0..hlen]);
		try out.appendSlice(a, rem[0..hlen]);
		const result = if (preserve)
			try deflate.inspect(std.heap.page_allocator, rem[hlen..], .crc32)
		else try deflate.optimize(a, &out, rem[hlen..], options, .crc32);
		const end = hlen + result.consumed;
		if (end + 8 > rem.len) return error.Malformed;
		const trailer = rem[end..][0..8];
		if (result.checksum != rdint_le(u32, trailer, 0) or
			@as(u32, @truncate(result.decoded_size)) != rdint_le(u32, trailer, 4)) return error.Malformed;
		try out.appendSlice(a, trailer);
		pos += end + 8;
	}
	return if (preserve or (!allow_growth and out.items.len > in.len)) in else out.items;
}

/// Bit-exact assembly of one member; concatenation and padding are refused.
/// This structural roundtrip does not validate the payload checksum.
pub fn roundtrip(a: std.mem.Allocator, in: []const u8) ![]const u8 {
	const hlen = headerLen(in) orelse return error.Malformed;
	const raw = in[hlen .. in.len - 8];
	var out: std.ArrayList(u8) = .empty;
	try out.appendSlice(a, in[0..hlen]);
	if (try deflate.roundtrip(a, &out, raw) != raw.len) return error.Malformed;
	try out.appendSlice(a, in[in.len - 8 ..]);
	return out.items;
}

const measure = @import("deflmeasure.zig");
const Statistics = measure.Statistics;
const ERR: i64 = -1;
pub fn count(data: []const u8, stats: ?*Statistics) i64 {
	// Walk every member, including BGZF. Check framing, not header flags or checksums.
	if (data.len == 0) return ERR;
	var total: i64 = 0;
	var pos: usize = 0;
	while (pos < data.len) {
		const rem = data[pos..];
		const hlen = parseHeader(rem, false) orelse return ERR;
		var r = @import("deflcommon.zig").BitReader{ .data = rem[hlen..] };
		const bits = measure.countReader(&r, stats);
		if (bits < 0) return ERR;
		const consumed = (r.pos() + 7) / 8;
		if (hlen + consumed + 8 > rem.len) return ERR; // missing member trailer
		total += bits;
		pos += hlen + consumed + 8;
	}
	return total;
}

