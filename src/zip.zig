//! ZIP directory parsing, lossless assembly and per-entry optimization.

const std = @import("std");
const deflate = @import("deflopt.zig");
const byteio = @import("byteio.zig");
const rdint_le = byteio.rdint_le;
const wrint_le = byteio.wrint_le;

const ParseError = error{ Malformed, OutOfMemory };

// ── ZIP container ─────────────────────────────────────────────────────────
//
// Central-directory-driven walker. Local headers can omit sizes
// under a data descriptor (GP flag bit 3), so the CD is authoritative. Every
// field is captured VERBATIM (slices into `data`, no copies); on re-encoding
// only the compressed size (local header + data descriptor + CD record) and the
// local-header offsets (CD records + EOCD) are rewritten. CRC-32 and
// uncompressed size are invariant under re-encoding and never touched.

pub const ZIP_LFH_SIG = [4]u8{ 'P', 'K', 3, 4 }; // 0x04034b50 local file header
pub const ZIP_CDH_SIG = [4]u8{ 'P', 'K', 1, 2 }; // 0x02014b50 central directory header
pub const ZIP_EOCD_SIG = [4]u8{ 'P', 'K', 5, 6 }; // 0x06054b50 end of central directory
pub const ZIP_DD_SIG = [4]u8{ 'P', 'K', 7, 8 }; // 0x08074b50 data-descriptor signature
pub const ZIP_Z64_LOC_SIG = [4]u8{ 'P', 'K', 6, 7 }; // 0x07064b50 zip64 EOCD locator
pub const APK_SIG_BLOCK_MAGIC = "APK Sig Block 42"; // 16 bytes preceding the CD

pub const ZIP_FLAG_ENCRYPTED: u16 = 0x0001; // GP flag bit 0
pub const ZIP_FLAG_DATA_DESC: u16 = 0x0008; // GP flag bit 3
pub const ZIP_METHOD_DEFLATE: u16 = 8;
const ZIP_EXTRA_ZIP64: u16 = 0x0001;

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
	// Replacement payload set by optimize before assembly:
	new_data: ?[]const u8 = null,

	pub fn outData(self: ZipEntry) []const u8 {
		return self.new_data orelse self.data;
	}
};

pub const ZipArchive = struct {
	prefix: []const u8, // bytes before the first local header (SFX stub, etc.)
	entries: []ZipEntry, // in CENTRAL-DIRECTORY order
	physical_order: []const usize, // entry indices in local-header order
	eocd: []const u8, // end record, comment and opaque suffix, verbatim
	prefix_bias: i64, // actual_cd_start - EOCD's cd_offset field
	passthrough: bool = false, // zip64 / APK-sig-block: whole file emitted unchanged
	raw: []const u8 = &.{}, // original bytes, kept for passthrough emission
};

/// Check directory framing before treating a signature in a comment/suffix as
/// an end record. ZIP64 is handled by whole-file passthrough in the parser.
fn zipEocdHasDirectory(data: []const u8, end: usize) bool {
	const entries = rdint_le(u16, data, end + 10);
	const size    = rdint_le(u32, data, end + 12);
	if (entries == 0xffff or rdint_le(u16, data, end + 8) == 0xffff or size == 0xffffffff or
		rdint_le(u32, data, end + 16) == 0xffffffff or
		(end >= 20 and std.mem.eql(u8, data[end - 20 .. end - 16], &ZIP_Z64_LOC_SIG))) return true;
	if (size > end) return false;
	var pos = end - size;
	for (0..entries) |_| {
		if (end - pos < 46 or !std.mem.eql(u8, data[pos .. pos + 4], &ZIP_CDH_SIG)) return false;
		const len = 46 + @as(usize, rdint_le(u16, data, pos + 28)) + rdint_le(u16, data, pos + 30) + rdint_le(u16, data, pos + 32);
		if (len > end - pos) return false;
		pos += len;
	}
	return pos == end;
}

/// Prefer a complete archive ending at EOF, then allow an arbitrary suffix.
/// The parser retains every byte from the selected end record through EOF.
fn zipFindEocd(data: []const u8) ?usize {
	if (data.len < 22) return null;
	for ([_]bool{ false, true }) |suffix| {
		const lo: usize = if (!suffix and data.len > 22 + 0xffff) data.len - 22 - 0xffff else 0;
		var idx = data.len - 22;
		while (true) {
			if (std.mem.eql(u8, data[idx .. idx + 4], &ZIP_EOCD_SIG)) {
				const end = idx + 22 + @as(usize, rdint_le(u16, data, idx + 20));
				if ((if (suffix) end < data.len else end == data.len) and zipEocdHasDirectory(data, idx)) return idx;
			}
			if (idx == lo) break;
			idx -= 1;
		}
	}
	return null;
}

/// True if a local/central extra field carries a Zip64 Extended Information
/// block (header ID 0x0001) — the authoritative per-entry zip64 marker even
/// when totals fit in 32 bits.
fn zipExtraHasZip64(extra: []const u8) bool {
	var p: usize = 0;
	while (p + 4 <= extra.len) {
		const hid  = rdint_le(u16, extra, p    );
		const size = rdint_le(u16, extra, p + 2);
		if (hid == ZIP_EXTRA_ZIP64) return true;
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

fn passthroughArchive(data: []const u8, eocd: []const u8) ZipArchive {
	return .{ .prefix = &.{}, .entries = &.{}, .physical_order = &.{}, .eocd = eocd, .prefix_bias = 0, .passthrough = true, .raw = data };
}

/// Walk a ZIP container via its central directory. error.Malformed on multi-disk
/// archives. Bytes after the comment remain opaque. Zip64 / APK-signing-block containers are
/// DETECTED and returned with passthrough=true (whole-file byte-exact emission).
pub fn parseZipMembers(alloc: std.mem.Allocator, data: []const u8) ParseError!ZipArchive {
	const eocd_pos = zipFindEocd(data) orelse return error.Malformed;

	const disk_no       = rdint_le(u16, data, eocd_pos +  4);
	const cd_disk       = rdint_le(u16, data, eocd_pos +  6);
	const cd_count_disk = rdint_le(u16, data, eocd_pos +  8);
	const total_entries = rdint_le(u16, data, eocd_pos + 10);
	const cd_size       = rdint_le(u32, data, eocd_pos + 12);
	const cd_offset     = rdint_le(u32, data, eocd_pos + 16);

	if (disk_no != 0 or cd_disk != 0) return error.Malformed; // multi-disk

	const eocd = data[eocd_pos..];

	// Zip64 detection: a zip64 EOCD locator immediately precedes the EOCD, or a
	// sentinel sits in a count/size/offset field.
	var zip64 = (eocd_pos >= 20 and std.mem.eql(u8, data[eocd_pos - 20 .. eocd_pos - 16], &ZIP_Z64_LOC_SIG));
	if (total_entries == 0xFFFF or cd_count_disk == 0xFFFF or cd_size == 0xFFFFFFFF or cd_offset == 0xFFFFFFFF) zip64 = true;
	if (zip64) return passthroughArchive(data, eocd);
	if (cd_count_disk != total_entries) return error.Malformed;

	if (cd_size > eocd_pos) return error.Malformed; // CD size overruns file start
	const actual_cd_start = eocd_pos - cd_size;

	// APK v2/v3 signing block sits between the last entry and the CD, ending in a
	// 16-byte magic immediately before the CD. Any rewrite bricks the signature.
	if (actual_cd_start >= 16 and std.mem.eql(u8, data[actual_cd_start - 16 .. actual_cd_start], APK_SIG_BLOCK_MAGIC))
		return passthroughArchive(data, eocd);

	const prefix_bias: i64 = @as(i64, @intCast(actual_cd_start)) - @as(i64, cd_offset);

	// ---- pass 1: walk the central directory (authoritative) ----
	var entries: std.ArrayList(ZipEntry) = .empty;
	var p: usize = actual_cd_start;
	var i: usize = 0;
	while (i < total_entries) : (i += 1) {
		if (p + 46 > data.len or !std.mem.eql(u8, data[p .. p + 4], &ZIP_CDH_SIG)) return error.Malformed;
		const gp         = rdint_le(u16, data, p +  8);
		const method     = rdint_le(u16, data, p + 10);
		const crc        = rdint_le(u32, data, p + 16);
		const comp       = rdint_le(u32, data, p + 20);
		const uncomp     = rdint_le(u32, data, p + 24);
		const n: usize   = rdint_le(u16, data, p + 28);
		const m: usize   = rdint_le(u16, data, p + 30);
		const k: usize   = rdint_le(u16, data, p + 32);
		const disk_start = rdint_le(u16, data, p + 34);
		const local_off  = rdint_le(u32, data, p + 42);
		if (disk_start != 0 and disk_start != 0xFFFF) return error.Malformed; // multi-disk
		const cdh_len = 46 + n + m + k;
		if (p + cdh_len > data.len) return error.Malformed; // truncated CD record
		const cdh = data[p .. p + cdh_len];
		const cd_extra = cdh[46 + n .. 46 + n + m];
		if (comp == 0xFFFFFFFF or uncomp == 0xFFFFFFFF or local_off == 0xFFFFFFFF or zipExtraHasZip64(cd_extra))
			return passthroughArchive(data, eocd);
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
		const ln: usize = rdint_le(u16, data, lh_pos + 26);
		const lm: usize = rdint_le(u16, data, lh_pos + 28);
		const lfh_len = 30 + ln + lm;
		if (lh_pos + lfh_len > data.len) return error.Malformed;
		const lfh = data[lh_pos .. lh_pos + lfh_len];
		if (zipExtraHasZip64(lfh[30 + ln .. 30 + ln + lm]))
			return passthroughArchive(data, eocd);
		// Mismatched local-header and central-directory CRC/size fields are
		// a hard error, never silently normalized. With a data descriptor the
		// LFH fields must be all-zero (APPNOTE 4.4.4) or an exact mirror of the
		// CD values (attested writer pattern).
		const lfh_crc    = rdint_le(u32, data, lh_pos + 14);
		const lfh_comp   = rdint_le(u32, data, lh_pos + 18);
		const lfh_uncomp = rdint_le(u32, data, lh_pos + 22);
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
			if (rdint_le(u32, descriptor, base    ) != e.crc32 or
				rdint_le(u32, descriptor, base + 4) != e.comp_size or
				rdint_le(u32, descriptor, base + 8) != e.uncomp_size) return error.Malformed;
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
		.physical_order = phys,
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
	std.debug.assert(arc.physical_order.len == arc.entries.len);
	const new_lh_pos = try alloc.alloc(usize, arc.entries.len); // keyed by CD index
	for (arc.physical_order) |j| {
		const e = arc.entries[j];
		new_lh_pos[j] = out.items.len;
		const payload = e.outData();
		try out.appendSlice(alloc, e.lfh);
		// Rewrite the LFH compressed size when it carries one: always without a
		// descriptor; with one, only for the mirrored-sizes writer pattern
		// (parse validated the mirror, a re-encode must keep it honest) —
		// spec-zeroed fields stay zero.
		if (e.gp_flag & ZIP_FLAG_DATA_DESC == 0 or rdint_le(u32, e.lfh, 18) != 0)
			wrint_le(u32, out.items, new_lh_pos[j] + 18, @intCast(payload.len));
		try out.appendSlice(alloc, payload);
		if (e.descriptor.len > 0) {
			const start = out.items.len;
			const has_sig = std.mem.eql(u8, e.descriptor[0..4], &ZIP_DD_SIG);
			try out.appendSlice(alloc, e.descriptor);
			wrint_le(u32, out.items, start + @as(usize, if (has_sig) 8 else 4), @intCast(payload.len));
		}
		try out.appendSlice(alloc, e.pad);
	}

	const new_cd_start = out.items.len;
	for (arc.entries, 0..) |e, j| { // CD order preserved
		const start = out.items.len;
		try out.appendSlice(alloc, e.cdh);
		wrint_le(u32, out.items, start + 20, @intCast(e.outData().len));
		wrint_le(u32, out.items, start + 42, @intCast(@as(i64, @intCast(new_lh_pos[j])) - arc.prefix_bias));
	}
	const new_cd_size = out.items.len - new_cd_start;

	const end_start = out.items.len;
	try out.appendSlice(alloc, arc.eocd);
	wrint_le(u32, out.items, end_start + 12, @intCast(new_cd_size));
	wrint_le(u32, out.items, end_start + 16, @intCast(@as(i64, @intCast(new_cd_start)) - arc.prefix_bias));
	return out.items;
}


pub fn optimize(a: std.mem.Allocator, in: []const u8, options: deflate.Options, allow_growth: bool) ![]const u8 {
	const arc = try parseZipMembers(a, in);
	if (arc.passthrough) return in;
	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	for (arc.entries) |*e| {
		if (e.method != ZIP_METHOD_DEFLATE or e.gp_flag & ZIP_FLAG_ENCRYPTED != 0) continue;
		_ = scratch.reset(.{ .retain_with_limit = 8 << 20 });
		const es = scratch.allocator();
		var out: std.ArrayList(u8) = .empty;
		out.ensureTotalCapacity(es, e.data.len) catch continue;
		const result = deflate.optimize(es, &out, e.data, options, .crc32) catch |err| switch (err) {
			error.VerificationFailed => return err,
			else => continue,
		};
		// Invalid payloads remain opaque; directory consistency is independent.
		if (result.checksum != e.crc32 or result.decoded_size != e.uncomp_size) continue;
		if (allow_growth or out.items.len < e.data.len) {
			e.new_data = try a.dupe(u8, out.items);
		}
	}
	const result = try assembleZipMembers(a, arc);
	return if (!allow_growth and result.len > in.len) in else result;
}

const measure = @import("deflmeasure.zig");
const Statistics = measure.Statistics;
const ERR: i64 = -1;

test "ZIP suffix survives roundtrip and optimization" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	// One DEFLATE entry containing a stored run of 32 A bytes, plus a comment.
	const hex = "504b0304140000000800af18555d1e6f31ad25000000200000000100000061012000dfff" ++
		"4141414141414141414141414141414141414141414141414141414141414141" ++
		"504b01021403140000000800af18555d1e6f31ad250000002000000001000000000000000000000080010000000061" ++
		"504b050600000000010001002f000000440000000700636f6d6d656e74";
	var bytes: [hex.len / 2]u8 = undefined;
	const base = try std.fmt.hexToBytes(&bytes, hex);
	const long_suffix = [_]u8{0xa5} ** 65536;
	var false_end = [_]u8{0} ** 22;
	@memcpy(false_end[0..4], &ZIP_EOCD_SIG);
	false_end[8] = 1;
	false_end[10] = 1;
	wrint_le(u32, &false_end, 12, 46); // No directory precedes this suffix signature.
	for ([_]bool{ false, true }) |fast| {
		const options: deflate.Options = .{ .reparse = !fast };
		for ([_][]const u8{ &.{}, "SFX prefix" }) |prefix| {
			const original = try std.mem.concat(a, u8, &.{ prefix, base });
			const optimized = try optimize(a, original, options, false);
			try std.testing.expect(optimized.len < original.len);
			for ([_][]const u8{ "\x00\xffsuffixPK\x05\x06", &long_suffix, &false_end }) |suffix| {
				const input = try std.mem.concat(a, u8, &.{ original, suffix });
				try std.testing.expectEqualSlices(u8, input, try assembleZipMembers(a, try parseZipMembers(a, input)));
				const expected = try std.mem.concat(a, u8, &.{ optimized, suffix });
				try std.testing.expectEqualSlices(u8, expected, try optimize(a, input, options, false));
			}
		}
	}
	const empty = ZIP_EOCD_SIG ++ [_]u8{0} ** 18;
	const empty_with_suffix = try std.mem.concat(a, u8, &.{ &empty, &long_suffix });
	try std.testing.expectEqualSlices(u8, empty_with_suffix, try optimize(a, empty_with_suffix, .{}, false));
}

pub fn count(data: []const u8, s: *Statistics) i64 {
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer arena.deinit();
	const arc = parseZipMembers(arena.allocator(), data) catch return ERR;
	if (arc.passthrough) {
		s.opaque_streams += 1;
		return 0;
	}
	var total: i64 = 0;
	for (arc.entries) |entry| {
		if (entry.method != ZIP_METHOD_DEFLATE) continue;
		if (entry.gp_flag & ZIP_FLAG_ENCRYPTED != 0) {
			s.opaque_streams += 1;
			continue;
		}
		const bits = measure.count(entry.data, s);
		if (bits < 0) return ERR;
		total += bits;
	}
	return total;
}
