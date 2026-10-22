//! RFC 1950 framing and Adler-32 validation around one DEFLATE stream.
const std = @import("std");
const deflate = @import("deflopt.zig");

const CM_DEFLATE = 8;
const MAX_CINFO = 7; // 32 KiB window
const FDICT = 0x20;

fn supportedHeader(header: *const [2]u8) bool {
	const cmf: u16 = header[0];
	const flg: u16 = header[1];
	return cmf & 15 == CM_DEFLATE and cmf >> 4 <= MAX_CINFO and (cmf * 256 + flg) % 31 == 0 and flg & FDICT == 0;
}

/// Header and trailer are preserved. Dictionary-dependent streams and extra
/// bytes between the final DEFLATE block and Adler-32 are refused.
pub fn optimize(a: std.mem.Allocator, in: []const u8, options: deflate.Options) deflate.StreamError![]u8 {
	if (in.len < 6 or !supportedHeader(in[0..2])) return error.Malformed;
	var out: std.ArrayList(u8) = .empty;
	try out.ensureTotalCapacity(a, in.len);
	try out.appendSlice(a, in[0..2]);
	const raw = in[2 .. in.len - 4];
	const result = try deflate.optimize(a, &out, raw, options, .adler32);
	if (result.consumed != raw.len or result.checksum != std.mem.readInt(u32, in[in.len - 4 ..][0..4], .big)) return error.Malformed;
	try out.appendSlice(a, in[in.len - 4 ..]);
	return out.items;
}

const measure = @import("deflmeasure.zig");
/// Measure the payload without checking Adler-32.
pub fn count(data: []const u8) error{Malformed}!measure.Statistics {
	if (data.len < 8 or !supportedHeader(data[0..2])) return error.Malformed;
	return measure.count(data[2 .. data.len - 4]);
}
