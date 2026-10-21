//! Linux CLI for raw DEFLATE, gzip, PNG and ZIP optimization.
//!
//! FILE arguments are rewritten in place with a durable sibling backup.
//! -r walks directories and selects files by signature. -i/-o selects pair
//! mode; without files, stdin and stdout carry a binary stream.
//!
//! I/O uses Linux syscalls. The work queue and counters use atomics; each
//! status line uses a single write. Optimizer invariant failures abort.

const std = @import("std");
const Args = @import("cli_args.zig").Args;
const linux = std.os.linux;
const deflopt = @import("deflopt.zig");
const containers = @import("containers.zig");

const BAK_SUFFIX = ".unflate-bak";
const AT_FDCWD = linux.AT.FDCWD;

// ── syscall helpers ─────────────────────────────────────────────────────────

fn sysErr(rc: usize) !usize {
	const errno = linux.errno(rc);
	if (errno != .SUCCESS) {
		inline for (std.meta.fields(linux.E)) |field| {
			if (errno == @field(linux.E, field.name)) return @field(anyerror, field.name);
		}
		return error.UnknownErrno;
	}
	return rc;
}

fn sysOpen(pz: [*:0]const u8, flags: linux.O, mode: linux.mode_t) !i32 {
	return @intCast(try sysErr(linux.openat(AT_FDCWD, pz, flags, mode)));
}

fn writeAllFd(fd: i32, bytes: []const u8) !void {
	var off: usize = 0;
	while (off < bytes.len) {
		off += try sysErr(linux.write(fd, bytes.ptr + off, bytes.len - off));
	}
}

/// Formatted print to fd 1/2 as ONE write(2) — no lock needed for line
/// integrity. Output is low-volume status text; truncation at 4 KB is fine.
fn fdPrint(fd: i32, comptime fmt: []const u8, args: anytype) void {
	var buf: [4096]u8 = undefined;
	const s = std.fmt.bufPrint(&buf, fmt, args) catch blk: {
		break :blk buf[0..];
	};
	writeAllFd(fd, s) catch {};
}

fn readWholeFile(alloc: std.mem.Allocator, pz: [*:0]const u8) ![]u8 {
	const fd = try sysOpen(pz, .{ .ACCMODE = .RDONLY, .CLOEXEC = true }, 0);
	defer _ = linux.close(fd);
	return readAllFd(alloc, fd);
}

fn readAllFd(alloc: std.mem.Allocator, fd: i32) ![]u8 {
	var data: std.ArrayList(u8) = .empty;
	var chunk: [1 << 16]u8 = undefined;
	while (true) {
		const n = try sysErr(linux.read(fd, &chunk, chunk.len));
		if (n == 0) break;
		try data.appendSlice(alloc, chunk[0..n]);
	}
	return data.items;
}

fn statxAt(pz: [*:0]const u8) !linux.Statx {
	var stx: linux.Statx = undefined;
	_ = try sysErr(linux.statx(AT_FDCWD, pz, 0, .{
		.TYPE = true,
		.MODE = true,
		.UID = true,
		.GID = true,
		.SIZE = true,
		.ATIME = true,
		.MTIME = true,
		.INO = true,
	}, &stx));
	return stx;
}

fn pathZ(alloc: std.mem.Allocator, path: []const u8) ![:0]const u8 {
	return alloc.dupeZ(u8, path);
}

fn isatty(fd: i32) bool {
	_ = std.posix.tcgetattr(fd) catch return false;
	return true;
}

// ── format detection ─────────────────────────

const Kind = containers.Format;
var format_override: ?Kind = null;
var options: containers.Options = .{}; // Set before workers start; read-only thereafter.
var report_format = false;

fn selectFormat(data: []const u8) ?Kind {
	const detected = detect(data);
	if (report_format) fdPrint(2, "format: {s}\n", .{if (detected) |k| @tagName(k) else "unknown"});
	return format_override orelse detected;
}

const detect = containers.detect;
fn sniffHead(head: []const u8) bool { return containers.sniff(head) != null; }

var explore_stats_wanted: bool = false;

fn optimizeBytes(alloc: std.mem.Allocator, kind: Kind, data: []const u8, source: []const u8) ![]const u8 {
	defer if (explore_stats_wanted) printExploreStats(source);
	return containers.optimize(alloc, kind, data, options);
}

fn optimizeError(e: anyerror) []const u8 {
	return switch (e) {
		error.UnsafePngChunk => "UnsafePngChunk: rewriting IDAT requires --discard-unsafe-chunks (removes metadata)",
		error.UnknownCriticalPngChunk => "UnknownCriticalPngChunk: cannot safely interpret this PNG",
		else => @errorName(e),
	};
}

// ── in-place write ───────────────────

fn copyXattr(alloc: std.mem.Allocator, source: i32, backup: i32, name: [*:0]const u8) !void {
	var empty: [0]u8 = .{};
	const size = try sysErr(linux.fgetxattr(source, name, &empty, 0));
	const value = try alloc.alloc(u8, size);
	defer alloc.free(value);
	const n = try sysErr(linux.fgetxattr(source, name, value.ptr, value.len));
	if (n > value.len) return error.MetadataChanged;
	_ = try sysErr(linux.fsetxattr(backup, name, value.ptr, n, 0));
}

fn copyXattrs(alloc: std.mem.Allocator, source: i32, backup: i32) !void {
	var empty: [0]u8 = .{};
	const rc = linux.flistxattr(source, &empty, 0);
	if (linux.errno(rc) == .OPNOTSUPP) return;
	const names = try alloc.alloc(u8, try sysErr(rc));
	defer alloc.free(names);
	const n = try sysErr(linux.flistxattr(source, names.ptr, names.len));
	if (n > names.len) return error.MetadataChanged;
	// Drop any ACL inherited from the directory; it need not exist on source.
	const removed = linux.fremovexattr(@intCast(backup), "system.posix_acl_access");
	if (linux.errno(removed) != .NODATA and linux.errno(removed) != .OPNOTSUPP)
		_ = try sysErr(removed);
	// Set the source ACL last: it may remove our permission to set other xattrs.
	var acl: ?[*:0]const u8 = null;
	var it = std.mem.splitScalar(u8, names[0..n], 0);
	while (it.next()) |name| {
		if (name.len == 0) continue;
		const namez: [*:0]const u8 = @ptrCast(name.ptr);
		if (std.mem.eql(u8, name, "system.posix_acl_access")) {
			acl = namez;
		} else try copyXattr(alloc, source, backup, namez);
	}
	if (acl) |name| try copyXattr(alloc, source, backup, name);
}

/// Rewrite the existing inode, preserving its identity. Exclusively create
/// and fsync a sibling backup with copied metadata before truncation.
/// Remove new backups if preparation or the truncating open fails; retain recovery data
/// if rewriting and in-process repair both fail. An existing backup always
/// refuses the operation. The rewritten inode itself is not fsynced.
fn writeInplace(alloc: std.mem.Allocator, path: []const u8, data: []const u8, original: []const u8, stx: linux.Statx) !void {
	const pz = try pathZ(alloc, path);
	const bakz = try std.mem.concatWithSentinel(alloc, u8, &.{ path, BAK_SUFFIX }, 0);
	const times = [2]linux.timespec{
		.{ .sec = stx.atime.sec, .nsec = stx.atime.nsec },
		.{ .sec = stx.mtime.sec, .nsec = stx.mtime.nsec },
	};
	var backup_created = false;
	var rewrite_started = false;
	errdefer if (backup_created and !rewrite_started) {
		_ = linux.unlinkat(AT_FDCWD, bakz, 0);
	};
	{
		const bfd = try sysOpen(bakz, .{ .ACCMODE = .WRONLY, .CREAT = true, .EXCL = true, .CLOEXEC = true }, 0o600);
		backup_created = true;
		defer _ = linux.close(bfd);
		// A restrictive umask/default ACL must not prevent metadata copying.
		_ = try sysErr(linux.fchmod(bfd, 0o600));
		try writeAllFd(bfd, original);
		var bst: linux.Statx = undefined;
		_ = try sysErr(linux.statx(bfd, "", linux.AT.EMPTY_PATH, .{ .UID = true, .GID = true }, &bst));
		if (bst.uid != stx.uid or bst.gid != stx.gid)
			_ = try sysErr(linux.fchown(bfd, stx.uid, stx.gid));
		const source = try sysOpen(pz, .{ .ACCMODE = .RDONLY, .CLOEXEC = true }, 0);
		defer _ = linux.close(source);
		try copyXattrs(alloc, source, bfd);
		_ = try sysErr(linux.fchmod(bfd, stx.mode & 0o7777));
		_ = try sysErr(linux.futimens(bfd, &times));
		_ = try sysErr(linux.fsync(bfd));
	}
	{
		// Make the backup's dirent durable before touching the target.
		const dirz = try alloc.dupeZ(u8, std.fs.path.dirname(path) orelse ".");
		const dfd = try sysOpen(dirz, .{ .ACCMODE = .RDONLY, .CLOEXEC = true }, 0);
		defer _ = linux.close(dfd);
		_ = try sysErr(linux.fsync(dfd));
	}
	inplace: {
		const fd = try sysOpen(pz, .{ .ACCMODE = .WRONLY, .TRUNC = true, .CLOEXEC = true }, 0);
		rewrite_started = true; // Truncation succeeded; failures now require repair.
		defer _ = linux.close(fd);
		writeAllFd(fd, data) catch break :inplace;
		_ = linux.utimensat(AT_FDCWD, pz, &times, 0);
		_ = linux.unlinkat(AT_FDCWD, bakz, 0);
		return;
	}
	// Write failed (ENOSPC/EIO/...): repair in place from the bytes we hold.
	repair: {
		const fd = sysOpen(pz, .{ .ACCMODE = .WRONLY, .TRUNC = true, .CLOEXEC = true }, 0) catch break :repair;
		defer _ = linux.close(fd);
		writeAllFd(fd, original) catch break :repair;
		_ = linux.unlinkat(AT_FDCWD, bakz, 0); // repaired; backup served its purpose
		return error.WriteFailed;
	}
	// Repair failed too: KEEP the backup, report the failure.
	return error.WriteFailed;
}

// ── per-file processing ─────────────────────────────────────────────────────

const Status = enum { opt, nogain, skip, err };

const Result = struct {
	status: Status,
	insize: usize = 0,
	outsize: usize = 0,
	msg: []const u8 = "",
};

fn processOne(alloc: std.mem.Allocator, path: []const u8) Result {
	const pz = pathZ(alloc, path) catch return .{ .status = .err, .msg = "OutOfMemory" };
	// Snapshot times before the read bumps atime.
	const stx = statxAt(pz) catch |e|
		return .{ .status = .err, .msg = @errorName(e) };
	const data = readWholeFile(alloc, pz) catch |e|
		return .{ .status = .err, .msg = @errorName(e) };
	const kind = selectFormat(data) orelse
		return .{ .status = .skip, .insize = data.len, .outsize = data.len, .msg = "not PNG/gzip/zip" };
	const out = optimizeBytes(alloc, kind, data, path) catch |e|
		return .{ .status = .err, .msg = optimizeError(e) };
	if (!options.allow_growth and out.len >= data.len)
		return .{ .status = .nogain, .insize = data.len, .outsize = data.len, .msg = @tagName(kind) };
	writeInplace(alloc, path, out, data, stx) catch |e|
		return .{ .status = .err, .msg = @errorName(e) };
	return .{ .status = .opt, .insize = data.len, .outsize = out.len, .msg = @tagName(kind) };
}

// ── target collection ───────────────────────────

fn usageExit(comptime fmt: []const u8, args: anytype) noreturn {
	fdPrint(2, fmt ++ "\n", args);
	std.process.exit(1);
}

fn lessStr(_: void, a: []const u8, b: []const u8) bool {
	return std.mem.order(u8, a, b) == .lt;
}

const DT_UNKNOWN = 0;
const DT_DIR = 4;
const DT_REG = 8;
const DT_LNK = 10;

/// Walk with one open directory descriptor. Follow symlinks to regular
/// files, but do not descend into symlinked directories.
fn walkDir(alloc: std.mem.Allocator, dir_path: []const u8, files: *std.ArrayList([]const u8)) !void {
	var pending: std.ArrayList([]const u8) = .empty;
	defer pending.deinit(alloc);
	try pending.append(alloc, dir_path);
	var buf: [16384]u8 = undefined;
	while (pending.pop()) |dir| {
		const dz = try pathZ(alloc, dir);
		const fd = sysOpen(dz, .{ .ACCMODE = .RDONLY, .DIRECTORY = true, .CLOEXEC = true }, 0) catch continue;
		defer _ = linux.close(fd);
		while (true) {
			const n = try sysErr(linux.getdents64(fd, &buf, buf.len));
			if (n == 0) break;
			var off: usize = 0;
			while (off < n) {
				const ent: *align(1) linux.dirent64 = @ptrCast(&buf[off]);
				const name = std.mem.span(@as([*:0]u8, @ptrCast(&ent.name)));
				const etype = ent.type;
				off += ent.reclen;
				if (std.mem.eql(u8, name, ".") or std.mem.eql(u8, name, "..")) continue;
				const full = try std.fs.path.join(alloc, &.{ dir, name });
				switch (etype) {
					DT_DIR => try pending.append(alloc, full),
					DT_REG => try files.append(alloc, full),
					DT_LNK, DT_UNKNOWN => {
						const stx = statxAt(try pathZ(alloc, full)) catch continue;
						if (stx.mode & linux.S.IFMT == linux.S.IFREG)
							try files.append(alloc, full)
						else if (etype == DT_UNKNOWN and stx.mode & linux.S.IFMT == linux.S.IFDIR)
							try pending.append(alloc, full);
					},
					else => {},
				}
			}
		}
	}
}

const InoKey = struct { dev_major: u32, dev_minor: u32, ino: u64 };

fn collectTargets(
	alloc: std.mem.Allocator,
	names: []const []const u8,
	recursive: bool,
	targets: *std.ArrayList([]const u8),
	sniffed_out: *usize,
) !void {
	// Deduplicate hard links and repeated paths by (device, inode).
	var seen = std.AutoHashMap(InoKey, void).init(alloc);
	for (names) |name| {
		const nz = try pathZ(alloc, name);
		const stx = statxAt(nz) catch |e| usageExit("error: {s}: {s}", .{ name, @errorName(e) });
		if (stx.mode & linux.S.IFMT == linux.S.IFDIR) {
			if (!recursive) usageExit("error: {s} is a directory (use -r to recurse)", .{name});
			var files: std.ArrayList([]const u8) = .empty;
			try walkDir(alloc, name, &files);
			std.mem.sort([]const u8, files.items, {}, lessStr); // Stable processing order.
			for (files.items) |p| {
				if (std.mem.endsWith(u8, p, BAK_SUFFIX)) {
					// A leftover crash backup is recovery data, never an optimization target.
					sniffed_out.* += 1;
					continue;
				}
				var head: [8]u8 = undefined;
				const fdr = sysOpen(try pathZ(alloc, p), .{ .ACCMODE = .RDONLY, .CLOEXEC = true }, 0) catch {
					sniffed_out.* += 1;
					continue;
				};
				const hn = sysErr(linux.read(fdr, &head, head.len)) catch 0;
				_ = linux.close(fdr);
				if (format_override != null or sniffHead(head[0..hn])) {
					try addTarget(alloc, &seen, targets, p);
				} else {
					sniffed_out.* += 1;
				}
			}
		} else {
			try addTarget(alloc, &seen, targets, name);
		}
	}
}

fn addTarget(
	alloc: std.mem.Allocator,
	seen: *std.AutoHashMap(InoKey, void),
	targets: *std.ArrayList([]const u8),
	path: []const u8,
) !void {
	const stx = statxAt(try pathZ(alloc, path)) catch {
		try targets.append(alloc, path); // let processOne report the error
		return;
	};
	const gop = try seen.getOrPut(.{ .dev_major = stx.dev_major, .dev_minor = stx.dev_minor, .ino = stx.ino });
	if (!gop.found_existing) try targets.append(alloc, path);
}

// ── batch runner ──────────────────────────────────────

const BatchCtx = struct {
	targets: []const []const u8,
	verbose: bool,
	next: std.atomic.Value(usize) = .init(0),
	n_opt: std.atomic.Value(usize) = .init(0),
	n_nogain: std.atomic.Value(usize) = .init(0),
	n_skip: std.atomic.Value(usize) = .init(0),
	n_err: std.atomic.Value(usize) = .init(0),
	saved: std.atomic.Value(i64) = .init(0),
};

fn report(ctx: *BatchCtx, path: []const u8, r: Result) void {
	switch (r.status) {
		.opt => {
			_ = ctx.n_opt.fetchAdd(1, .monotonic);
			_ = ctx.saved.fetchAdd(@as(i64, @intCast(r.insize)) - @as(i64, @intCast(r.outsize)), .monotonic);
			fdPrint(1, "{s}: {d} B -> {d} B (saved {d} B, {s})\n", .{ path, r.insize, r.outsize, @as(i64, @intCast(r.insize)) - @as(i64, @intCast(r.outsize)), r.msg });
		},
		.err => {
			_ = ctx.n_err.fetchAdd(1, .monotonic);
			fdPrint(1, "{s}: ERROR  {s}\n", .{ path, r.msg });
		},
		.nogain => {
			_ = ctx.n_nogain.fetchAdd(1, .monotonic);
			if (ctx.verbose) fdPrint(1, "{s}: already optimal\n", .{path});
		},
		.skip => {
			_ = ctx.n_skip.fetchAdd(1, .monotonic);
			if (ctx.verbose) fdPrint(1, "{s}: skipped: {s}\n", .{ path, r.msg });
		},
	}
}

fn batchWorker(ctx: *BatchCtx) void {
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer arena.deinit();
	while (true) {
		const i = ctx.next.fetchAdd(1, .monotonic);
		if (i >= ctx.targets.len) return;
		const path = ctx.targets[i];
		const r = processOne(arena.allocator(), path);
		report(ctx, path, r);
		_ = arena.reset(.{ .retain_with_limit = 8 << 20 });
	}
}

fn runBatch(alloc: std.mem.Allocator, targets: []const []const u8, jobs: usize, verbose: bool, sniffed_out: usize) u8 {
	var ctx: BatchCtx = .{ .targets = targets, .verbose = verbose };
	const nthreads = @min(@max(jobs, 1), targets.len);
	if (nthreads <= 1) {
		batchWorker(&ctx);
	} else spawn: {
		const threads = alloc.alloc(std.Thread, nthreads) catch {
			batchWorker(&ctx);
			break :spawn;
		};
		var spawned: usize = 0;
		for (threads) |*t| {
			t.* = std.Thread.spawn(.{}, batchWorker, .{&ctx}) catch break;
			spawned += 1;
		}
		if (spawned == 0) batchWorker(&ctx);
		for (threads[0..spawned]) |t| t.join();
	}
	const skipped = ctx.n_skip.load(.monotonic) + sniffed_out;
	fdPrint(1, "{d} file(s) | {d} optimized (saved {d} B) | {d} already optimal | {d} skipped | {d} error(s)\n", .{
		targets.len,               ctx.n_opt.load(.monotonic), ctx.saved.load(.monotonic),
		ctx.n_nogain.load(.monotonic), skipped,               ctx.n_err.load(.monotonic),
	});
	return if (ctx.n_err.load(.monotonic) > 0) 1 else 0;
}

// ── pair mode ──────────────────────────────────────────

fn runPair(alloc: std.mem.Allocator, in_path: []const u8, out_path: []const u8, overwrite: bool) u8 {
	const oz = pathZ(alloc, out_path) catch usageExit("error: out of memory", .{});
	var stream = false;
	if (statxAt(oz)) |ost| {
		const kind = ost.mode & linux.S.IFMT;
		stream = kind == linux.S.IFCHR or kind == linux.S.IFIFO;
		if (kind == linux.S.IFDIR) usageExit("error: output path is a directory", .{});
		if (!stream and !overwrite) usageExit("error: output path exists (pass -y to overwrite)", .{});
	} else |_| {}
	const iz = pathZ(alloc, in_path) catch usageExit("error: out of memory", .{});
	const ist = statxAt(iz) catch |e| usageExit("error: {s}: {s}", .{ in_path, @errorName(e) });
	const data = readWholeFile(alloc, iz) catch usageExit("error: cannot read: {s}", .{in_path});
	const kind = selectFormat(data) orelse usageExit("error: {s}: not PNG/gzip/zip", .{in_path});
	const out = optimizeBytes(alloc, kind, data, in_path) catch |e|
		usageExit("error: {s}: {s}", .{ in_path, optimizeError(e) });
	if (!options.allow_growth and out.len >= data.len and !stream) {
		fdPrint(1, "{s}: already optimal ({d} B, {s}) — no output written\n", .{ in_path, data.len, @tagName(kind) });
		return 0;
	}
	{
		const fd = sysOpen(oz, .{ .ACCMODE = .WRONLY, .CREAT = true, .TRUNC = true, .CLOEXEC = true }, 0o666) catch
			usageExit("error: cannot write: {s}", .{out_path});
		defer _ = linux.close(fd);
		writeAllFd(fd, out) catch usageExit("error: write failed: {s}", .{out_path});
		// copystat: mode + times (the meaningful subset of shutil.copystat here).
		if (!stream) _ = linux.fchmod(fd, ist.mode & 0o7777);
	}
	const times = [2]linux.timespec{
		.{ .sec = ist.atime.sec, .nsec = ist.atime.nsec },
		.{ .sec = ist.mtime.sec, .nsec = ist.mtime.nsec },
	};
	if (!stream) _ = linux.utimensat(AT_FDCWD, oz, &times, 0);
	fdPrint(1, "{s}: {d} B -> {d} B (saved {d} B, {s}) -> {s}\n", .{ in_path, data.len, out.len, @as(i64, @intCast(data.len)) - @as(i64, @intCast(out.len)), @tagName(kind), out_path });
	return 0;
}

/// Drain this input's counters on the thread that performed its optimization.
fn printExploreStats(source: []const u8) void {
	const s = deflopt.takeExploreStats();
	fdPrint(2, "explore-stats reads={d}/{d}/{d} hits={d}/{d}/{d} confirms={d} confirm_gains={d} rounds={d} full_ties={d} agree_single={d} disagree_single={d} agree_assemble={d} disagree_assemble={d} input={s}\n", .{
		s.reads[0], s.reads[1], s.reads[2], s.hits[0], s.hits[1], s.hits[2], s.confirms, s.confirm_gains, s.rounds, s.full_ties,
		s.agree[1], s.disagree[1], s.agree[2], s.disagree[2], source,
	});
}

// ── filter mode ─────────────────────────────────────────────────────────────

fn runFilter(alloc: std.mem.Allocator) u8 {
	const data = readAllFd(alloc, 0) catch |e| {
		if (e != error.OutOfMemory)
			fdPrint(2, "error: reading stdin: {s}\n", .{@errorName(e)});
		return 1;
	};
	const kind = selectFormat(data) orelse usageExit("error: stdin is not PNG/gzip/zip", .{});
	const out = optimizeBytes(alloc, kind, data, "<stdin>") catch |e|
		usageExit("error: {s}", .{optimizeError(e)});
	writeAllFd(1, out) catch return 1;
	return 0;
}

// ── main / arg parsing ──────────────────────────────────────────────────────

const HELP =
	\\usage: unflate [-r] [-j N] [-v] FILE|DIR...
	\\       unflate -i IN -o OUT [-y]
	\\       unflate < IN > OUT
	\\
	\\Losslessly shrink DEFLATE streams in PNG/gzip/zip files using
	\\re-encoding and bounded reparsing. Files are rewritten in place
	\\(into the inode, crash backup alongside) and left untouched when there
	\\is no byte gain, unless --allow-growth is specified.
	\\
	\\  -r, --recursive   recurse into directory arguments
	\\  -i, --input IN    explicit input (pair mode, with -o)
	\\  -o, --output OUT  explicit output (pair mode, with -i)
	\\  -y                overwrite an existing output file (pair mode)
	\\  -j, --jobs N      worker threads (default: half the cores)
	\\  -v, --verbose     also print already-optimal and skipped files
	\\  --format TYPE     auto (default), deflate, gzip, png or zip
	\\  --allow-growth    write results even without byte savings (default: off)
	\\  --discard-unsafe-chunks  omit unknown unsafe PNG chunks when needed (default: off)
	\\  --report-format   report automatically detected type on stderr
	\\  --fast            skip LZ77 reparsing; retain tree/token re-encoding
	\\  --min-dist-codes N  distance codewords every rebuilt tree must carry:
	\\                    2 (default) complete trees, readable by every decoder
	\\                    1 single 1-bit code allowed (zlib >= 1.2.2)
	\\                    0 max-optimal; Windows Explorer rejects some outputs
	\\  --explore-read G  candidate evaluation: full|single|assemble (default: full)
	\\  --feedback-read G completion evaluation (default: as --explore-read)
	\\  --feedback-order O completion order: creation|assembled|mixed (default: creation)
	\\  --cheap-contexts  use single-pass results to seed further searches (default: off)
	\\  --confirm-margin N  fully evaluate candidates within N bits of the best (default: 0)
	\\  --confirm-winner  fully evaluate each reparse round winner (default: off)
	\\  --explore-stats   print per-input evaluation counters to stderr (default: off)
	\\  --measure-agreement  compare cheaper evaluations against full (default: off)
	\\  --version         print native build identity and exit
	\\  -h, --help        this help
	\\  --                treat remaining arguments as filenames
	\\
	\\Value options also accept --name=value, -jN, -iIN and -oOUT.
	\\
;

// Translate the shared cursor's missing-value error into this CLI's usage exit.
fn option(args: *Args, long: []const u8, short: []const u8) ?[]const u8 {
	return args.option(long, short) catch usageExit("error: {s} needs a value", .{
		if (short.len != 0) short else long,
	});
}

pub fn main(init: std.process.Init.Minimal) !void {
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer arena.deinit();
	const alloc = arena.allocator();

	var args = Args{ .argv = init.args.vector[1..] };

	var files: std.ArrayList([]const u8) = .empty;
	var recursive = false;
	var in_path: ?[]const u8 = null;
	var out_path: ?[]const u8 = null;
	var overwrite = false;
	var verbose = false;
	var jobs: usize = @max(1, (std.Thread.getCpuCount() catch 2) / 2);

	while (args.next()) |arg| {
		if (args.flag("-r") or args.flag("--recursive")) {
			recursive = true;
		} else if (args.flag("-y")) {
			overwrite = true;
		} else if (args.flag("-v") or args.flag("--verbose")) {
			verbose = true;
		} else if (args.flag("--allow-growth")) {
			options.allow_growth = true;
		} else if (args.flag("--discard-unsafe-chunks")) {
			options.discard_unsafe_chunks = true;
		} else if (args.flag("--report-format")) {
			report_format = true;
		} else if (option(&args, "--format", "")) |value| {
			format_override = if (std.mem.eql(u8, value, "auto")) null else
				std.meta.stringToEnum(Kind, value) orelse usageExit("error: --format expects auto|deflate|gzip|png|zip", .{});
		} else if (args.flag("--fast")) {
			options.stream.reparse = false;
		} else if (option(&args, "--min-dist-codes", "")) |value| {
			options.stream.min_dist_codes = std.fmt.parseInt(u8, value, 10) catch 255;
			if (options.stream.min_dist_codes > 2) usageExit("error: --min-dist-codes expects 0, 1 or 2, got {s}", .{value});
		} else if (option(&args, "--explore-read", "")) |value| {
			options.stream.explore_read.grade = std.meta.stringToEnum(deflopt.ExploreRead.Grade, value) orelse
				usageExit("error: --explore-read expects full|single|assemble, got {s}", .{value});
		} else if (option(&args, "--feedback-read", "")) |value| {
			options.stream.explore_read.feedback_grade = std.meta.stringToEnum(deflopt.ExploreRead.Grade, value) orelse
				usageExit("error: --feedback-read expects full|single|assemble, got {s}", .{value});
		} else if (option(&args, "--feedback-order", "")) |value| {
			options.stream.feedback_policy.order = std.meta.stringToEnum(deflopt.FeedbackOrder, value) orelse
				usageExit("error: --feedback-order expects creation|assembled|mixed, got {s}", .{value});
		} else if (args.flag("--cheap-contexts")) {
			options.stream.feedback_policy.cheap_contexts = true;
		} else if (option(&args, "--confirm-margin", "")) |value| {
			options.stream.explore_read.margin = std.fmt.parseInt(i64, value, 10) catch
				usageExit("error: --confirm-margin expects an integer, got {s}", .{value});
		} else if (args.flag("--confirm-winner")) {
			options.stream.explore_read.winner_always = true;
		} else if (args.flag("--explore-stats")) {
			explore_stats_wanted = true;
		} else if (args.flag("--measure-agreement")) {
			explore_stats_wanted = true;
			options.stream.explore_read.measure_agreement = true;
		} else if (args.flag("--version")) {
			fdPrint(1, "{s}", .{@import("deflversion.zig").text});
			return;
		} else if (args.flag("-h") or args.flag("--help")) {
			fdPrint(1, HELP, .{});
			return;
		} else if (option(&args, "--input", "-i")) |value| {
			in_path = value;
		} else if (option(&args, "--output", "-o")) |value| {
			out_path = value;
		} else if (option(&args, "--jobs", "-j")) |value| {
			jobs = std.fmt.parseInt(usize, value, 10) catch
				usageExit("error: -j expects a number, got {s}", .{value});
		} else if (args.options and arg.len > 1 and arg[0] == '-') {
			usageExit("error: unknown option: {s}", .{arg});
		} else {
			try files.append(alloc, arg);
		}
	}

	if (in_path != null or out_path != null) {
		if (in_path == null or out_path == null)
			usageExit("error: -i and -o must be used together", .{});
		if (files.items.len > 0)
			usageExit("error: positional files cannot be combined with -i/-o", .{});
		std.process.exit(runPair(alloc, in_path.?, out_path.?, overwrite));
	}

	if (files.items.len == 0) {
		if (isatty(0)) {
			fdPrint(1, HELP, .{});
			std.process.exit(1);
		}
		std.process.exit(runFilter(alloc));
	}

	var targets: std.ArrayList([]const u8) = .empty;
	var sniffed_out: usize = 0;
	try collectTargets(alloc, files.items, recursive, &targets, &sniffed_out);
	if (targets.items.len == 0) {
		fdPrint(1, "0 file(s) | 0 optimized (saved 0 B) | 0 already optimal | {d} skipped | 0 error(s)\n", .{sniffed_out});
		return;
	}
	std.process.exit(runBatch(alloc, targets.items, jobs, verbose, sniffed_out));
}
