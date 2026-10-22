//! PNG/APNG framing, metadata policy and embedded zlib streams.

const std = @import("std");
const deflate = @import("deflopt.zig");
const zlib = @import("zlib.zig");
const byteio = @import("byteio.zig");
const rdint_be = byteio.rdint_be;

const SCRATCH_RESET: std.heap.ArenaAllocator.ResetMode = .{ .retain_with_limit = 8 << 20 };

pub const Options = struct {
	stream: deflate.Options = .{},
	allow_growth: bool = false,
	discard_unsafe_chunks: bool = false,
};

pub const PNG_SIG = [_]u8{ 0x89, 'P', 'N', 'G', '\r', '\n', 0x1a, '\n' };

const ColorType = enum(u8) {
	grayscale = 0,
	truecolor = 2,
	indexed = 3,
	grayscale_alpha = 4,
	truecolor_alpha = 6,
};

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

fn wrU32be(v: u32) [@sizeOf(u32)]u8 {
	var bytes: [@sizeOf(u32)]u8 = undefined;
	std.mem.writeInt(u32, &bytes, v, .big);
	return bytes;
}

const Chunk = struct { typ: []const u8, data: []const u8 };

fn selectStream(original: []const u8, reencoded: []const u8, allow_growth: bool) []const u8 {
	return if (!allow_growth and reencoded.len > original.len) original else reencoded;
}

test "PNG stream adoption rejects growth unless requested" {
	// Two valid zlib encodings of an empty payload: fixed and stored.
	const fixed  = &[_]u8{ 0x78, 0x01, 0x03, 0x00, 0x00, 0x00, 0x00, 0x01 };
	const stored = &[_]u8{ 0x78, 0x01, 0x01, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01 };
	try std.testing.expectEqualSlices(u8, fixed, selectStream(fixed, stored, false));
	try std.testing.expectEqualSlices(u8, stored, selectStream(fixed, stored, true));
	for ([_]bool{ false, true }) |allow_growth| {
		try std.testing.expectEqualSlices(u8, fixed, selectStream(stored, fixed, allow_growth));
		// Equal-sized rewrites are accepted, including padding normalization.
		const padded = &[_]u8{ 0x78, 0x01, 0x03, 0xfc, 0x00, 0x00, 0x00, 0x01 };
		try std.testing.expectEqualSlices(u8, fixed, selectStream(padded, fixed, allow_growth));
	}
}

/// Optimize supported auxiliary streams. Invalid payloads stay opaque;
/// verification failures remain optimizer bugs. Only adopted bytes outlive scratch.
fn optimizeChunkData(a: std.mem.Allocator, scratch: *std.heap.ArenaAllocator, typ: []const u8, data: []const u8, options: Options) []const u8 {
	const offset = pngCompressedOffset(typ, data) orelse return data;
	const zlib_data = data[offset..];
	if (zlib_data.len == 0) return data;
	defer _ = scratch.reset(SCRATCH_RESET);
	const opt = zlib.optimize(scratch.allocator(), zlib_data, options.stream) catch |err| switch (err) {
		error.VerificationFailed => @panic("BUG: auxiliary DEFLATE verification failed"),
		else => return data,
	};
	const selected = selectStream(zlib_data, opt, options.allow_growth);
	if (selected.ptr == zlib_data.ptr) return data;
	return std.mem.concat(a, u8, &.{ data[0..offset], selected }) catch return data;
}

test "unknown PNG auxiliary compression methods remain opaque" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	var scratch = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer scratch.deinit();
	// A valid stored empty zlib stream would shrink if the method were ignored.
	var payload = [_]u8{ 'n', 0, 1, 0x78, 0x01, 0x01, 0, 0, 0xff, 0xff, 0, 0, 0, 1 };
	for ([_][]const u8{ "zTXt", "iCCP" }) |typ| {
		for ([_]u8{ 1, 255 }) |method| {
			payload[2] = method;
			try std.testing.expectEqualSlices(u8, &payload, optimizeChunkData(arena.allocator(), &scratch, typ, &payload, .{}));
		}
	}
}

/// Optimize auxiliary streams and merge consecutive fdAT groups, adjusting
/// fcTL/fdAT sequence numbers. Compact chunks in place; recycle scratch per stream.
fn optimizePostIdatChunks(a: std.mem.Allocator, scratch: *std.heap.ArenaAllocator, chunks: []Chunk, options: Options) ![]Chunk {
	var kept: usize = 0;
	var seq_delta: u32 = 0;
	var i: usize = 0;
	while (i < chunks.len) {
		std.debug.assert(kept <= i);
		const c = chunks[i];
		if (std.mem.eql(u8, c.typ, "fcTL")) {
			if (c.data.len < 4) return error.Malformed;
			const seq = rdint_be(u32, c.data, 0);
			// Refuse malformed sequences rather than wrapping the subtraction.
			if (seq < seq_delta) return error.Malformed;
			const nd = if (seq_delta == 0) c.data else
				try std.mem.concat(a, u8, &.{ &wrU32be(seq - seq_delta), c.data[4..] });
			chunks[kept] = .{ .typ = c.typ, .data = nd };
			i += 1;
		} else if (std.mem.eql(u8, c.typ, "fdAT")) {
			if (c.data.len < 4) return error.Malformed;
			// Merge consecutive fdAT chunks for this frame.
			const ss = scratch.allocator();
			var zlib_data: std.ArrayList(u8) = .empty;
			const first_seq = rdint_be(u32, c.data, 0);
			if (first_seq < seq_delta) return error.Malformed; // see fcTL above
			var group_len: u32 = 0;
			while (i < chunks.len and std.mem.eql(u8, chunks[i].typ, "fdAT")) : (i += 1) {
				if (chunks[i].data.len < 4) return error.Malformed;
				try zlib_data.appendSlice(ss, chunks[i].data[4..]);
				group_len += 1;
			}
			const opt = zlib.optimize(ss, zlib_data.items, options.stream) catch |err| switch (err) {
				error.VerificationFailed => @panic("BUG: frame DEFLATE verification failed"),
				else => zlib_data.items,
			};
			const selected = selectStream(zlib_data.items, opt, options.allow_growth);
			const nd = try std.mem.concat(a, u8, &.{ &wrU32be(first_seq - seq_delta), selected });
			chunks[kept] = .{ .typ = "fdAT", .data = nd };
			seq_delta += group_len - 1; // merged N→1
			_ = scratch.reset(SCRATCH_RESET);
		} else {
			chunks[kept] = .{ .typ = c.typ, .data = optimizeChunkData(a, scratch, c.typ, c.data, options) };
			i += 1;
		}
		kept += 1;
	}
	return chunks[0..kept];
}

test "post-IDAT APNG chunks require complete sequence fields" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	var scratch = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer scratch.deinit();
	const sequence = [_]u8{ 0, 0, 0, 0 };
	for (0..4) |length| {
		for ([_][]const u8{ "fcTL", "fdAT" }) |typ| {
			var chunks = [_]Chunk{.{ .typ = typ, .data = sequence[0..length] }};
			try std.testing.expectError(error.Malformed, optimizePostIdatChunks(arena.allocator(), &scratch, &chunks, .{}));
		}
		var chunks = [_]Chunk{
			.{ .typ = "fdAT", .data = &sequence },
			.{ .typ = "fdAT", .data = sequence[0..length] },
		};
		try std.testing.expectError(error.Malformed, optimizePostIdatChunks(arena.allocator(), &scratch, &chunks, .{}));
	}
}

fn writePngChunk(a: std.mem.Allocator, out: *std.ArrayList(u8), typ: []const u8, data: []const u8) !void {
	try out.appendSlice(a, &wrU32be(@intCast(data.len)));
	const start = out.items.len;
	try out.appendSlice(a, typ);
	try out.appendSlice(a, data);
	try out.appendSlice(a, &wrU32be(std.hash.crc.Crc32.hash(out.items[start..])));
}

/// Whether a chunk prevents rewriting IDAT without explicit removal permission.
/// These known chunks depend on pixels, palette, color interpretation or frame
/// controls, all preserved by our stream rewrites; none depend on IDAT encoding.
fn unsafePngChunk(typ: []const u8) bool {
	std.debug.assert(typ.len == 4);
	if (typ[0] & 0x20 == 0 or typ[3] & 0x20 != 0) return false;
	inline for (.{
		"bKGD", "cHRM", "cICP", "cLLI", "gAMA", "hIST", "iCCP", "mDCV",
		"sBIT", "sPLT", "sRGB", "tIME", "tRNS", "acTL", "fcTL", "fdAT",
	}) |known| {
		if (std.mem.eql(u8, typ, known)) return false;
	}
	return true;
}

pub fn optimize(a: std.mem.Allocator, in: []const u8, options: Options) ![]const u8 {

	if (in.len < 8 or !std.mem.eql(u8, in[0..8], &PNG_SIG)) return error.Malformed;

	var pre: std.ArrayList(Chunk) = .empty;
	var post: std.ArrayList(Chunk) = .empty;
	var idat: std.ArrayList(u8) = .empty;
	var seen_idat = false;
	var seen_plte = false;
	var seen_iend = false;
	var depth: u8 = 0;
	var color: ColorType = .grayscale;
	var unsafe_chunks = false;
	var idat_count: usize = 0;

	// Every byte must belong to a well-formed chunk; IDAT must be consecutive.
	var pos: usize = 8;
	var prev_was_idat = false;
	while (pos < in.len) {
		if (pos + 8 > in.len) return error.Malformed;
		const len: usize = @intCast(rdint_be(u32, in, pos));
		if (len > 0x7FFFFFFF) return error.Malformed;
		if (pos + 12 + len > in.len) return error.Malformed;
		const typ = in[pos + 4 .. pos + 8];
		const cdata = in[pos + 8 .. pos + 8 + len];
		for (typ) |letter| if (!std.ascii.isAlphabetic(letter)) return error.Malformed;
		const ihdr = std.mem.eql(u8, typ, "IHDR");
		const plte = std.mem.eql(u8, typ, "PLTE");
		const is_idat = std.mem.eql(u8, typ, "IDAT");
		const iend = std.mem.eql(u8, typ, "IEND");
		const idot = std.mem.eql(u8, typ, "iDOT");
		if (typ[0] & 0x20 == 0 and !ihdr and !plte and !is_idat and !iend)
			return error.UnknownCriticalPngChunk;
		if ((pos == 8) != ihdr or seen_iend) return error.Malformed;
		if (ihdr) {
			if (len != 13) return error.Malformed;
			const width = rdint_be(u32, cdata, 0);
			const height = rdint_be(u32, cdata, 4);
			depth = cdata[8];
			color = std.enums.fromInt(ColorType, cdata[9]) orelse return error.Malformed;
			const valid_depth = switch (color) {
				.grayscale => depth == 1 or depth == 2 or depth == 4 or depth == 8 or depth == 16,
				.truecolor, .grayscale_alpha, .truecolor_alpha => depth == 8 or depth == 16,
				.indexed => depth == 1 or depth == 2 or depth == 4 or depth == 8,
			};
			if (width == 0 or width > 0x7fffffff or height == 0 or height > 0x7fffffff or
				!valid_depth or cdata[10] != 0 or cdata[11] != 0 or cdata[12] > 1) return error.Malformed;
		}
		if (plte) {
			if (seen_plte or seen_idat or color == .grayscale or color == .grayscale_alpha or
				len == 0 or len > 768 or len % 3 != 0) return error.Malformed;
			if (color == .indexed and len / 3 > @as(usize, 1) << @intCast(depth)) return error.Malformed;
			seen_plte = true;
		}
		if (iend) {
			if (len != 0 or !seen_idat) return error.Malformed;
			seen_iend = true;
		}
		unsafe_chunks = unsafe_chunks or (!idot and unsafePngChunk(typ));
		const crc = std.hash.crc.Crc32.hash(in[pos + 4 .. pos + 8 + len]);
		if (crc != rdint_be(u32, in, pos + 8 + len)) return error.Malformed;
		if (is_idat) {
			if (color == .indexed and !seen_plte) return error.Malformed;
			if (seen_idat and !prev_was_idat) return error.Malformed;
			idat_count += 1;
			try idat.appendSlice(a, cdata);
			seen_idat = true;
			prev_was_idat = true;
		} else {
			// iDOT contains decoding-speed hints tied to encoded offsets.
			// Even auxiliary chunk rewrites can invalidate them.
			if (!idot) {
				const chunks = if (seen_idat) &post else &pre;
				try chunks.append(a, .{ .typ = typ, .data = cdata });
			}
			prev_was_idat = false;
		}
		pos += 12 + len;
	}
	if (!seen_iend or idat.items.len < 6) return error.Malformed;

	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	const new_idat = selectStream(idat.items, try zlib.optimize(a, idat.items, options.stream), options.allow_growth);
	const critical_changed = idat_count != 1 or !std.mem.eql(u8, idat.items, new_idat);
	const discard = critical_changed and options.discard_unsafe_chunks;
	if (critical_changed and unsafe_chunks and !discard) {
		return error.UnsafePngChunk;
	}
	if (discard) {
		for ([_]*std.ArrayList(Chunk){ &pre, &post }) |chunks| {
			var kept: usize = 0;
			for (chunks.items) |c| {
				if (unsafePngChunk(c.typ)) continue;
				chunks.items[kept] = c;
				kept += 1;
			}
			chunks.shrinkRetainingCapacity(kept);
		}
	}

	// Optimize auxiliary chunks.
	for (pre.items) |*c| c.data = optimizeChunkData(a, &scratch, c.typ, c.data, options);
	const new_post = try optimizePostIdatChunks(a, &scratch, post.items, options);

	// Assemble.
	var buf: std.ArrayList(u8) = .empty;
	try buf.appendSlice(a, &PNG_SIG);
	for (pre.items) |c| try writePngChunk(a, &buf, c.typ, c.data);
	try writePngChunk(a, &buf, "IDAT", new_idat);
	for (new_post) |c| try writePngChunk(a, &buf, c.typ, c.data);
	// File-level byte no-regress guard.
	if (!options.allow_growth and buf.items.len > in.len) return in;
	return buf.items;
}

test "PNG: truncated zlib streams are refused or kept before std.compress.flate reads them" {
	// Fuzz-minimized: std.compress.flate (Zig 0.16) fails an assertion on the
	// first stream and overflows on the second, both truncated mid-token. As
	// IDAT they must be refused; as zTXt kept verbatim.
	const truncated = [_][]const u8{
		&.{
			0x78, 0xda, 0xbd, 0xd3, 0xc5, 0x42, 0x10, 0x48, 0x00, 0x00, 0xd0, 0x01,
			0x24, 0xa4, 0x94, 0x6e, 0x44, 0x45, 0x94, 0xee, 0x0e, 0x09, 0x05, 0x25,
			0x45, 0x51, 0x41, 0xba, 0xbb, 0xbb, 0x95, 0x06, 0x95, 0x52, 0x29, 0x51,
			0x40, 0x09, 0x09, 0x30, 0x14, 0x69, 0x04, 0x94, 0xee, 0xee, 0xee, 0xee,
			0xae, 0xbd, 0xcd, 0x65, 0xef, 0x73, 0x7b, 0x3f, 0xf0, 0x00, 0xff, 0x30,
			0xff, 0x30, 0x30, 0x30, 0x30,
		},
		&.{
			0x78, 0xda, 0xed, 0xda, 0x01, 0x66, 0xc6, 0x40, 0x10, 0x86, 0xe1, 0xf7,
			0x37, 0x30, 0x30, 0x30,
		},
	};
	// 1x1 grayscale; the IDAT stream is one stored block holding [0, 0].
	const ihdr = [_]u8{ 0, 0, 0, 1, 0, 0, 0, 1, 8, 0, 0, 0, 0 };
	const idat = [_]u8{ 0x78, 0x01, 0x01, 0x02, 0x00, 0xfd, 0xff, 0x00, 0x00, 0x00, 0x02, 0x00, 0x01 };
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	for ([_]bool{ true, false }) |reparse_on| {
		for (truncated) |z| {
			var bad: std.ArrayList(u8) = .empty;
			try bad.appendSlice(a, &PNG_SIG);
			try writePngChunk(a, &bad, "IHDR", &ihdr);
			try writePngChunk(a, &bad, "IDAT", z);
			try writePngChunk(a, &bad, "IEND", "");
			try std.testing.expectError(error.Malformed, optimize(a, bad.items, .{ .stream = .{ .reparse = reparse_on } }));

			var ztxt: std.ArrayList(u8) = .empty;
			try writePngChunk(a, &ztxt, "zTXt", try std.mem.concat(a, u8, &.{ "Comment\x00\x00", z }));
			var aux: std.ArrayList(u8) = .empty;
			try aux.appendSlice(a, &PNG_SIG);
			try writePngChunk(a, &aux, "IHDR", &ihdr);
			try aux.appendSlice(a, ztxt.items);
			try writePngChunk(a, &aux, "IDAT", &idat);
			try writePngChunk(a, &aux, "IEND", "");
			const result = try optimize(a, aux.items, .{ .stream = .{ .reparse = reparse_on } });
			try std.testing.expect(result.len <= aux.items.len);
			try std.testing.expect(std.mem.indexOf(u8, result, ztxt.items) != null);
		}
	}
}


const measure = @import("deflmeasure.zig");
const Statistics = measure.Statistics;
const ERR: i64 = -1;
/// Count auxiliary DEFLATE bits (zTXt, iCCP, compressed iTXt). Invalid or
/// unsupported payloads contribute zero. Frame reassembly is handled in count.
fn countAuxChunk(typ: []const u8, cdata: []const u8, stats: ?*Statistics) i64 {
	const international = std.mem.eql(u8, typ, "iTXt");
	if (!international and !std.mem.eql(u8, typ, "zTXt") and !std.mem.eql(u8, typ, "iCCP")) return 0;
	if (international) {
		// Flag zero denotes ordinary text, not an opaque compressed stream.
		if (std.mem.indexOfScalar(u8, cdata, 0)) |nul| {
			if (nul + 1 < cdata.len and cdata[nul + 1] == 0) return 0;
		}
	}
	if (stats != null or international) {
		const data = if (pngCompressedOffset(typ, cdata)) |offset| cdata[offset..] else null;
		return countOptionalStream(data, stats);
	}
	// Historical zTXt/iCCP counters ignore the compression method byte.
	const nul = std.mem.indexOfScalar(u8, cdata, 0) orelse return 0;
	if (nul + 2 > cdata.len) return 0;
	const bits = zlib.count(cdata[nul + 2 ..], null);
	return if (bits < 0) 0 else bits;
}

/// Roll back partial measurements and legality when an optional stream fails.
fn countOptionalStream(data: ?[]const u8, stats: ?*Statistics) i64 {
	const saved = if (stats) |s| s.* else Statistics{};
	const saved_class = measure.worst_class;
	const bits = if (data) |bytes| zlib.count(bytes, stats) else ERR;
	if (bits >= 0) return bits;
	if (stats) |s| {
		s.* = saved;
		s.opaque_streams += 1;
	}
	measure.worst_class = saved_class;
	return 0;
}

pub fn count(data: []const u8, stats: ?*Statistics) i64 {
	if (data.len < 8 or !std.mem.eql(u8, data[0..8], &PNG_SIG)) return ERR;

	// Measurement concatenates all IDAT, including malformed chunk ordering.
	const alloc = std.heap.page_allocator;
	var idat: std.ArrayList(u8) = .empty;
	defer idat.deinit(alloc);

	// APNG frame data spans multiple consecutive fdAT chunks: only the first per
	// frame carries the zlib header and the final deflate block lands in the last
	// fragment. Accumulate each run of consecutive fdAT payloads (4-byte sequence
	// number stripped) and count it as one zlib stream; a non-fdAT chunk (e.g.
	// fcTL) delimits the next frame. Counting a single fragment standalone
	// undercounts the frame.
	var frame: std.ArrayList(u8) = .empty;
	defer frame.deinit(alloc);
	var frame_present = false;
	var frame_malformed = false;

	var aux_total: i64 = 0;
	var pos: usize = 8;
	while (pos + 8 <= data.len) {
		const length: usize = @intCast(rdint_be(u32, data, pos));
		if (pos + 12 + length > data.len) {
			if (stats != null) return ERR;
			break;
		}
		const typ = data[pos + 4 .. pos + 8];
		const cdata = data[pos + 8 .. pos + 8 + length];
		const is_idat = std.mem.eql(u8, typ, "IDAT");
		const is_fdat = std.mem.eql(u8, typ, "fdAT");
		// Actual groups end at every non-fdAT chunk. Preserve historical
		// counters' cross-IDAT grouping for malformed chunk orders only.
		if (frame_present and !is_fdat and (stats != null or !is_idat)) {
			// Historical counters ignore short fdAT fragments.
			aux_total += countOptionalStream(if (stats != null and frame_malformed) null else frame.items, stats);
			frame.clearRetainingCapacity();
			frame_present = false;
			frame_malformed = false;
		}
		if (is_idat) {
			idat.appendSlice(alloc, cdata) catch return ERR;
		} else if (is_fdat) {
			frame_present = true;
			if (cdata.len >= 4) {
				frame.appendSlice(alloc, cdata[4..]) catch return ERR;
			} else {
				frame_malformed = true;
			}
		} else {
			aux_total += countAuxChunk(typ, cdata, stats);
		}
		pos += 12 + length;
	}
	if (frame_present) { // trailing frame (file ends on fdAT)
		aux_total += countOptionalStream(if (stats != null and frame_malformed) null else frame.items, stats);
	}

	if (idat.items.len < 6) return ERR; // need zlib hdr(2) + adler(4)
	if (stats != null and pos != data.len) return ERR;
	const idat_bits = if (stats != null) zlib.count(idat.items, stats) else measure.count(idat.items[2 .. idat.items.len - 4], null);
	if (idat_bits < 0) return ERR; // IDAT failure propagates
	return idat_bits + aux_total;
}

