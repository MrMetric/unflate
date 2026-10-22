//! Format dispatch and whole-file policy. Each format owns its envelope.
const std = @import("std");
pub const deflate = @import("deflopt.zig");
const gzip = @import("gzip.zig");
const png = @import("png.zig");
const zip = @import("zip.zig");

pub const Format = enum { deflate, gzip, png, zip };
pub const Options = struct {
	stream: deflate.Options = .{},
	allow_growth: bool = false,
	discard_unsafe_chunks: bool = false,
};

pub fn sniff(data: []const u8) ?Format {
	if (data.len >= 8 and std.mem.eql(u8, data[0..8], &png.PNG_SIG)) return .png;
	if (data.len >= 2 and data[0] == 0x1f and data[1] == 0x8b) return .gzip;
	if (data.len >= 4 and (std.mem.eql(u8, data[0..4], &zip.ZIP_LFH_SIG) or
		std.mem.eql(u8, data[0..4], &zip.ZIP_EOCD_SIG) or
		std.mem.eql(u8, data[0..4], &zip.ZIP_CDH_SIG))) return .zip;
	return null;
}

pub fn detect(data: []const u8) ?Format {
	return sniff(data) orelse if (zip.looksLikeZip(data)) @as(?Format, .zip) else null;
}

/// Returned bytes live in `a` or alias `in`. Raw files preserve an opaque
/// suffix after the first stream; the stream module itself does not own it.
pub fn optimize(a: std.mem.Allocator, format: Format, in: []const u8, options: Options) ![]const u8 {
	return switch (format) {
		.gzip => try gzip.optimize(a, in, options.stream, options.allow_growth),
		.png => try png.optimize(a, in, .{ .stream = options.stream,
			.allow_growth = options.allow_growth, .discard_unsafe_chunks = options.discard_unsafe_chunks }),
		.zip => try zip.optimize(a, in, options.stream, options.allow_growth),
		.deflate => blk: {
			var out: std.ArrayList(u8) = .empty;
			const result = try deflate.optimize(a, &out, in, options.stream, .none);
			try out.appendSlice(a, in[result.consumed..]);
			break :blk if (!options.allow_growth and out.items.len > in.len) in else out.items;
		},
	};
}

test {
	std.testing.refAllDecls(@This());
	std.testing.refAllDecls(@import("deflmeasure.zig"));
}
