//! Raw DEFLATE re-encoding, bounded LZ77 reparsing and decoded-content verification.
//! Container framing and file policy live in the format modules.

const std = @import("std");
const common = @import("deflcommon.zig");
const deflasm = @import("deflasm.zig");
const reparse = @import("deflreparse.zig");
const ir = @import("deflir.zig");
const feedback = @import("deflfeedback.zig");
const encoding = @import("deflencoding.zig");
const freqToLengths = encoding.freqToLengths;
const dynBlockCost = encoding.bitCost;
const MAX_CL_SEQ = encoding.MAX_CL_SEQ;
const clHeaderBits = encoding.clHeaderBits;
const hclenOf = encoding.hclenOf;
const trim = encoding.trim;
const boundary = @import("deflboundary.zig");

const Block = deflasm.Block;
const Huff = deflasm.Huff;
const Token = deflasm.Token;
const ClEntry = deflasm.ClEntry;
const lenCodeTable = common.lenCodeTable;
const distCodeTable = common.distCodeTable;
const HCLEN_ORDER = common.HCLEN_ORDER;

// ── cost models ─────────────────────

const TIE_THRESHOLD: i64 = 5;
const MAX_NEAR_TIES: usize = 8;

/// Bound retained scratch capacity so one pathological block does not pin
/// memory for the rest of a file. Excess capacity is released at the next reset.
const SCRATCH_RETAIN_LIMIT: usize = 8 << 20;
const SCRATCH_RESET: std.heap.ArenaAllocator.ResetMode = .{ .retain_with_limit = SCRATCH_RETAIN_LIMIT };

const fixed_ll_bits = common.fixed_ll_lengths;

test "distance floor: built trees carry the configured codewords, inherited ones pass through" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const previous = swapMinDistCodes(2);
	defer _ = swapMinDistCodes(previous);

	// distFloor: only the single-symbol case changes; the filler takes the
	// lowest absent index and the used symbol is forced to one bit.
	var d = [_]u8{0} ** 30;
	d[5] = 3;
	distFloor(&d);
	try std.testing.expectEqual(@as(u8, 1), d[0]);
	try std.testing.expectEqual(@as(u8, 1), d[5]);
	try std.testing.expectEqual(@as(usize, 2), countNonzero(&d));
	d = [_]u8{0} ** 30;
	d[0] = 1;
	distFloor(&d);
	try std.testing.expectEqual(@as(u8, 1), d[1]);
	d = [_]u8{0} ** 30;
	d[3] = 1;
	d[7] = 1;
	distFloor(&d);
	try std.testing.expectEqual(@as(usize, 2), countNonzero(&d));
	try std.testing.expectEqual(@as(u8, 0), d[0]);
	d = [_]u8{0} ** 30;
	distFloor(&d);
	try std.testing.expectEqual(@as(usize, 0), countNonzero(&d));
	for ([_]u8{ 0, 1 }) |level| {
		_ = swapMinDistCodes(level);
		d = [_]u8{0} ** 30;
		d[5] = 1;
		distFloor(&d);
		try std.testing.expectEqual(@as(usize, 1), countNonzero(&d));
	}

	// Candidate sets per level and rebuilt trees.
	var lits: [48]Token = undefined;
	for (&lits, 0..) |*t, i| t.* = .{ .lit = @intCast(0x40 + i % 16) };
	var single: [52]Token = undefined;
	@memcpy(single[0..48], &lits);
	// Distance 5 is code 4: the level-2 filler at index 0 precedes a zero run,
	// so revoking it merges the run and pays (a trailing dead code's trim is
	// invisible to the structural screen).
	for (single[48..]) |*t| t.* = .{ .match = .{ .length = 3, .distance = 5 } };
	for ([_]u8{ 0, 1, 2 }) |level| {
		_ = swapMinDistCodes(level);
		const cands = encoding.emptyDistCandidates(min_dist_codes);
		try std.testing.expectEqual(@as(usize, if (level == 0) 2 else 1), cands.len);
		for (cands) |c| try std.testing.expect(countNonzero(c) >= level);
		const m = (try encoder().complete(a, &lits, true, .{})).body.huff;
		try std.testing.expect(countNonzero(m.dist_lengths) >= level);
		try std.testing.expectEqual(@as(usize, if (level == 2) 2 else 1), m.dist_lengths.len);
		const s = (try encoder().complete(a, &single, true, .{})).body.huff;
		try std.testing.expectEqual(@as(usize, if (level == 2) 2 else 1), countNonzero(s.dist_lengths));
		try std.testing.expectEqual(@as(u8, 1), s.dist_lengths[4]);
		try std.testing.expectEqual(@as(u8, if (level == 2) 1 else 0), s.dist_lengths[0]);
		// The floor is a property of what we build, never of what we read.
		try std.testing.expect(satisfiesDistFloor(.{ .is_last = true, .body = .{ .huff = s } }, .{ .is_last = true, .body = .{ .stored = "x" } }, level));
	}
	_ = swapMinDistCodes(2);
	const hazard = (try encoder().complete(a, &single, true, .{})).body.huff;
	var lone = [_]u8{1};
	var inherited = hazard;
	inherited.dist_lengths = &lone;
	const inherited_block: Block = .{ .is_last = true, .body = .{ .huff = inherited } };
	try std.testing.expect(!satisfiesDistFloor(inherited_block, .{ .is_last = true, .body = .{ .stored = "x" } }, 2));
	try std.testing.expect(satisfiesDistFloor(inherited_block, inherited_block, 2));
	try std.testing.expect(satisfiesDistFloor(.{ .is_last = true, .body = .{ .stored = "x" } }, inherited_block, 2));
	try std.testing.expect(satisfiesDistFloor(fixedHuffBlock(&single, true), inherited_block, 2));

	// The filler is a dead code. Under the floor the revoke is gated
	// and the polish keeps two codewords; without it the revoke pays.
	const floored = try polishLengths(a, hazard);
	if (floored) |r| try std.testing.expect(countNonzero(r.dist) >= 2);
	_ = swapMinDistCodes(0);
	const revoked = (try polishLengths(a, hazard)).?;
	try std.testing.expectEqual(@as(usize, 1), countNonzero(revoked.dist));

	// Trailing zero lengths (HDIST padding) do not change the code, so a
	// re-padded input tree is still inherited; a moved codeword is not.
	var d_padded_empty = [_]u8{ 0, 0 };
	var d_empty = [_]u8{0};
	var d_padded_lone = [_]u8{ 0, 0, 1, 0, 0 };
	var d_lone_at_2 = [_]u8{ 0, 0, 1 };
	var d_lone_at_1 = [_]u8{ 0, 1 };
	var padded_empty = inherited;
	padded_empty.dist_lengths = &d_padded_empty;
	var empty = inherited;
	empty.dist_lengths = &d_empty;
	var padded_lone = inherited;
	padded_lone.dist_lengths = &d_padded_lone;
	var lone_at_2 = inherited;
	lone_at_2.dist_lengths = &d_lone_at_2;
	var lone_at_1 = inherited;
	lone_at_1.dist_lengths = &d_lone_at_1;
	const block = struct {
		fn of(h: Huff) Block {
			return .{ .is_last = true, .body = .{ .huff = h } };
		}
	}.of;
	try std.testing.expect(satisfiesDistFloor(block(empty), block(padded_empty), 2));
	try std.testing.expect(satisfiesDistFloor(block(padded_empty), block(empty), 2));
	try std.testing.expect(satisfiesDistFloor(block(lone_at_2), block(padded_lone), 2));
	try std.testing.expect(!satisfiesDistFloor(block(lone_at_1), block(padded_lone), 2));
	try std.testing.expect(!satisfiesDistFloor(block(empty), block(lone_at_2), 1));
}

test "distance floor: a re-padded inherited empty tree is the floor-free answer" {
	// Fuzz-minimized: one dynamic block of literals whose
	// empty distance tree is sent with HDIST 2. Without reparsing, the
	// searches keep the empty tree at HDIST 1, which is the input's own code
	// and therefore inherited: the result must equal the floor-free one.
	const input = [_]u8{
		0x05, 0xc1, 0xd1, 0x09, 0x80, 0x40, 0x0c, 0x44, 0xc1, 0x56, 0x5e, 0x01,
		0x62, 0x1f, 0x96, 0x71, 0x62, 0xce, 0xcb, 0xc7, 0x11, 0x70, 0x17, 0xd2,
		0xbe, 0x30, 0xc9, 0x30, 0x30, 0xb9, 0x30, 0x30, 0x30, 0x30, 0x30, 0x4d,
		0x3a, 0xd4, 0x3e, 0xf9, 0x01,
	};
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const previous_floor = swapMinDistCodes(2);
	defer _ = swapMinDistCodes(previous_floor);
	for ([_]bool{ false, true }) |reparse_on| {
		const previous_reparse = swapReparse(reparse_on);
		defer _ = swapReparse(previous_reparse);
		_ = swapMinDistCodes(0);
		const free = try optimizeDeflateBytes(a, &input);
		_ = swapMinDistCodes(2);
		const floored = try optimizeDeflateBytes(a, &input);
		try std.testing.expect(inflateEql(&input, floored));
		try std.testing.expectEqualSlices(u8, free, floored);
	}
}

fn countNonzero(lengths: []const u8) usize {
	var n: usize = 0;
	for (lengths) |l| {
		if (l != 0) n += 1;
	}
	return n;
}

test "optimizer memo: tree polish counts, nulls, ownership and mode" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	var memo = try OptimizerMemo.init(std.testing.allocator, 1);
	defer memo.deinit();
	const previous = swapOptimizerMemo(null);
	defer _ = swapOptimizerMemo(previous);
	var tokens = [_]Token{.{ .lit = 65 }} ** 64;
	tokens[0] = .{ .lit = 66 };
	// Deliberately give the rare literal the shortest code.
	var seed_ll = [_]u8{0} ** (common.EOB + 1);
	seed_ll[65] = 2;
	seed_ll[66] = 1;
	seed_ll[common.EOB] = 2;
	var seed_dist = [_]u8{1};
	var saw_result = false;
	for ([_]bool{ false, true }) |t24| {
		cl_t24_arbitration = t24;
		defer cl_t24_arbitration = false;
		for (1..4) |n| {
			var h = fixedHuffBlock(tokens[0 .. n * 20], true).body.huff;
			h.ll_lengths = &seed_ll;
			h.dist_lengths = &seed_dist;
			const expected = try polishLengths(a, h);
			_ = swapOptimizerMemo(&memo);
			const misses = memo.polish_misses;
			const first = try polishLengths(a, h);
			try std.testing.expectEqual(misses + 1, memo.polish_misses);
			try std.testing.expectEqualDeep(expected, first);
			if (first) |r| {
				saw_result = true;
				r.ll[0] +%= 1;
			}
			const hits = memo.polish_hits;
			try std.testing.expectEqualDeep(expected, try polishLengths(a, h));
			try std.testing.expectEqual(hits + 1, memo.polish_hits);
			// Reordering literals preserves the memoized subproblem.
			std.mem.swap(Token, &tokens[0], &tokens[1]);
			try std.testing.expectEqualDeep(expected, try polishLengths(a, h));
			try std.testing.expectEqual(hits + 2, memo.polish_hits);
			std.mem.swap(Token, &tokens[0], &tokens[1]);
			_ = swapOptimizerMemo(null);
		}
	}
	try std.testing.expect(saw_result);
	// A minimal two-symbol tree has no profitable polish. Null is reusable.
	var ll = [_]u8{0} ** (common.EOB + 1);
	ll[65] = 1;
	ll[common.EOB] = 1;
	var dist = [_]u8{1};
	var h = fixedHuffBlock(tokens[1..2], true).body.huff;
	h.ll_lengths = &ll;
	h.dist_lengths = &dist;
	_ = swapOptimizerMemo(&memo);
	try std.testing.expectEqual(@as(?PolishResult, null), try polishLengths(a, h));
	const hits = memo.polish_hits;
	try std.testing.expectEqual(@as(?PolishResult, null), try polishLengths(a, h));
	try std.testing.expectEqual(hits + 1, memo.polish_hits);
	const misses = memo.polish_misses;
	cl_t24_arbitration = true;
	defer cl_t24_arbitration = false;
	_ = try polishLengths(a, h);
	try std.testing.expectEqual(misses + 1, memo.polish_misses);
}


const ClModel = encoding.Header;

/// Enable the all-literal and rep16-only CL seeds during the second
/// portfolio pass. The crossing chain always includes them. Thread-local
/// state prevents one worker from changing another worker's arbitration.
threadlocal var cl_t24_arbitration: bool = false;

/// Minimum number of codewords in rebuilt distance trees. Inherited trees
/// remain eligible unchanged. Level 0 permits empty and single-code trees;
/// level 1 requires a codeword; level 2 builds complete trees by adding a
/// one-bit filler at the lowest unused symbol when necessary.
/// The floor also applies to search costs: applying it only at emission
/// changes which candidates win. Each CLI worker owns its thread-local setting.
threadlocal var min_dist_codes: u8 = 2;
pub fn swapMinDistCodes(next: u8) u8 {
	std.debug.assert(next <= 2);
	const previous = min_dist_codes;
	min_dist_codes = next;
	return previous;
}
pub fn minDistCodes() u8 {
	return min_dist_codes;
}

/// Apply the floor to a freshly built 30-entry distance tree. freqToLengths
/// and mergeTree give a single used symbol a 1-bit code and >= 2 symbols a
/// complete tree, so only the single-symbol case needs the filler. The
/// filler's position is a materialization choice; the filler relocation move may
/// then park the dead code wherever the CL header prices it cheapest.
fn distFloor(dist_full: *[30]u8) void {
	encoding.applyFloor(dist_full, min_dist_codes);
}

/// Scoped per CLI worker thread.
threadlocal var reparse_enabled: bool = true;
threadlocal var boundary_search_enabled: bool = false;
threadlocal var boundary_slack: u32 = (boundary.Options{}).slack;
pub fn swapReparse(enabled: bool) bool {
	const previous = reparse_enabled;
	reparse_enabled = enabled;
	return previous;
}

/// Optional research override. Null selects the bounded production policy;
/// a session with zero evaluations selects the pre-extension reparse search.
pub const FeedbackSession = feedback.Session;
// ── Exploration read grade ───────────────

/// Grade of the read that the reparse walk and feedback controller apply to
/// each exploration candidate. `full` is production: the old portfolio closed
/// under restart (`optimizeBlockFast`). `single` is one classic configuration
/// pass. `assemble` is the materialized block's own exact cost, no polishing.
/// A candidate whose cheap cost is within `margin` bits of the record, or
/// the walk's round winner when `winner_always`, is re-read at full grade
/// before comparison. That read closes the fast portfolio, not the full
/// production reparse/feedback search. Default: production.
pub const ExploreRead = struct {
	pub const Grade = enum(u8) { full = 0, single = 1, assemble = 2 };
	grade: Grade = .full,
	/// Grade for the feedback controller's completions; null follows `grade`.
	feedback_grade: ?Grade = null,
	margin: i64 = 0,
	winner_always: bool = false,
	/// Under `full`, also read each walk variant at the cheaper grades and
	/// count whether they rank the round's two variants the same way.
	measure_agreement: bool = false,
};
pub const ExploreStats = struct {
	reads: [3]usize = .{ 0, 0, 0 },
	hits: [3]usize = .{ 0, 0, 0 },
	confirms: usize = 0,
	confirm_gains: usize = 0,
	rounds: usize = 0,
	full_ties: usize = 0,
	agree: [3]usize = .{ 0, 0, 0 },
	disagree: [3]usize = .{ 0, 0, 0 },
};
threadlocal var explore_read: ExploreRead = .{};
threadlocal var explore_stats: ExploreStats = .{};
pub fn swapExploreRead(next: ExploreRead) ExploreRead {
	const previous = explore_read;
	explore_read = next;
	return previous;
}
pub fn takeExploreStats() ExploreStats {
	const s = explore_stats;
	explore_stats = .{};
	return s;
}

pub const FeedbackOrder = feedback.Order;
/// Completion ordering and admission policy; defaults bound the production search.
pub const FeedbackPolicy = struct { order: FeedbackOrder = .creation, cheap_contexts: bool = false };
threadlocal var feedback_policy: FeedbackPolicy = .{};
pub fn swapFeedbackPolicy(next: FeedbackPolicy) FeedbackPolicy {
	const previous = feedback_policy;
	feedback_policy = next;
	return previous;
}
threadlocal var feedback_session: ?*FeedbackSession = null;
pub fn swapFeedbackSearch(session: ?*FeedbackSession) ?*FeedbackSession {
	const old = feedback_session;
	feedback_session = session;
	return old;
}

/// Exact tree, sweep, token-portfolio and encoded-read memos for related streams.
/// Direct-mapped slots bound storage and compare the full key after hashing;
/// collisions affect speed only. Results are copied to the caller's allocator.
/// Enabled within production reparsing. The owner must restore the
/// thread-local scope before freeing the memo (including on errors).
pub const OptimizerMemo = struct {
	const SweepKind = enum(u8) { section, structural };
	const SweepSlot = struct {
		valid: bool = false,
		len: u16 = 0,
		kind: SweepKind = .section,
		grant_cap: usize = 0,
		min_codes: usize = 0,
		lengths: [288]u8 = undefined,
		freqs: [288]u32 = undefined,
		prices: [19]i64 = undefined,
		output: [288]u8 = undefined,
		result: PolishPassResult = undefined,

		fn replay(self: *const SweepSlot, kind: SweepKind, seq: []u8, freqs: []const u32, prices: *const [19]i64, grant_cap: usize, min_codes: usize) ?PolishPassResult {
			if (!self.valid or self.len != seq.len or self.kind != kind or self.grant_cap != grant_cap or self.min_codes != min_codes or
				!std.mem.eql(u8, self.lengths[0..self.len], seq) or
				!std.mem.eql(u32, self.freqs[0..self.len], freqs) or
				!std.mem.eql(i64, &self.prices, prices)) return null;
			@memcpy(seq, self.output[0..self.len]);
			return self.result;
		}

		fn save(self: *SweepSlot, kind: SweepKind, input: []const u8, freqs: []const u32, prices: *const [19]i64, grant_cap: usize, min_codes: usize, output: []const u8, result: PolishPassResult) void {
			std.debug.assert(input.len == output.len and input.len == freqs.len);
			self.* = .{ .valid = true, .len = @intCast(input.len), .kind = kind, .grant_cap = grant_cap, .min_codes = min_codes,
				.prices = prices.*, .result = result };
			@memcpy(self.lengths[0..input.len], input);
			@memcpy(self.freqs[0..input.len], freqs);
			@memcpy(self.output[0..output.len], output);
		}
	};
	const StreamSlot = struct {
		arena: std.heap.ArenaAllocator,
		valid: bool = false,
		flags: u8 = 0,
		key: []const u64 = &.{},
		raw: []const u8 = &.{},
		portfolio: StreamPortfolio = undefined,
	};
	const PolishSlot = struct {
		valid: bool = false,
		ll_len: u16 = 0,
		dist_len: u16 = 0,
		t24: bool = false,
		floor: u8 = 0,
		lengths: [320]u8 = undefined,
		freqs: [320]u32 = undefined,
		result_ll_len: u16 = 0, // zero denotes a cached null result
		result_dist_len: u16 = 0,
		result: [320]u8 = undefined,
	};
	allocator: std.mem.Allocator,
	encoding: encoding.Memo,
	polish_slots: []PolishSlot,
	stream_slots: []StreamSlot,
	sweep_slots: []SweepSlot,
	projection: ProjectionMemo,
	polish_hits: u64 = 0,
	polish_misses: u64 = 0,
	portfolio_enabled: bool = true,
	portfolio_hits: u64 = 0,
	portfolio_misses: u64 = 0,
	sweep_hits: u64 = 0,
	sweep_misses: u64 = 0,

	pub fn init(allocator: std.mem.Allocator, capacity: usize) !OptimizerMemo {
		if (capacity == 0) return error.InvalidCapacity;
		var headers = try encoding.Memo.init(allocator, capacity);
		errdefer headers.deinit();
		const polish_slots = try allocator.alloc(PolishSlot, capacity);
		errdefer allocator.free(polish_slots);
		const stream_slots = try allocator.alloc(StreamSlot, @min(capacity, 16));
		errdefer allocator.free(stream_slots);
		const sweep_slots = try allocator.alloc(SweepSlot, @min(capacity, 1024));
		for (sweep_slots) |*entry| entry.valid = false;
		for (stream_slots) |*entry| entry.* = .{ .arena = std.heap.ArenaAllocator.init(allocator) };
		for (polish_slots) |*entry| entry.valid = false;
		return .{ .allocator = allocator, .encoding = headers, .polish_slots = polish_slots, .stream_slots = stream_slots, .sweep_slots = sweep_slots,
			.projection = .{ .inputs = std.heap.ArenaAllocator.init(allocator), .arena = std.heap.ArenaAllocator.init(allocator) } };
	}

	pub fn deinit(self: *OptimizerMemo) void {
		std.debug.assert(active_optimizer_memo != self);
		self.encoding.deinit();
		self.allocator.free(self.polish_slots);
		for (self.stream_slots) |*entry| entry.arena.deinit();
		self.allocator.free(self.stream_slots);
		self.allocator.free(self.sweep_slots);
		self.projection.deinit();
		self.* = undefined;
	}

	pub fn storageBytes(self: *const OptimizerMemo) usize {
		var bytes = self.encoding.storageBytes() + self.polish_slots.len * @sizeOf(PolishSlot) + self.stream_slots.len * @sizeOf(StreamSlot) + self.sweep_slots.len * @sizeOf(SweepSlot);
		for (self.stream_slots) |entry| bytes += entry.arena.queryCapacity();
		bytes += self.projection.inputs.queryCapacity() + self.projection.arena.queryCapacity();
		return bytes;
	}

	fn sweepSlot(self: *OptimizerMemo, kind: SweepKind, seq: []const u8, freqs: []const u32, prices: *const [19]i64, grant_cap: usize, min_codes: usize) *SweepSlot {
		var hash = std.hash.Wyhash.init(@intFromEnum(kind));
		hash.update(std.mem.asBytes(&grant_cap));
		hash.update(std.mem.asBytes(&min_codes));
		hash.update(seq);
		hash.update(std.mem.sliceAsBytes(freqs));
		hash.update(std.mem.asBytes(prices));
		return &self.sweep_slots[hash.final() % self.sweep_slots.len];
	}

	fn polishSlot(self: *OptimizerMemo, ll: []const u8, dist: []const u8, llf: []const u32, df: []const u32) *PolishSlot {
		var hash = std.hash.Wyhash.init(0);
		hash.update(&.{ @intCast(ll.len & 255), @intCast(ll.len >> 8), @intCast(dist.len), @intFromBool(cl_t24_arbitration), min_dist_codes });
		hash.update(ll);
		hash.update(dist);
		hash.update(std.mem.sliceAsBytes(llf));
		hash.update(std.mem.sliceAsBytes(df));
		return &self.polish_slots[hash.final() % self.polish_slots.len];
	}
};

threadlocal var active_optimizer_memo: ?*OptimizerMemo = null;

/// Return the previous scope so nested callers can restore it with defer.
pub fn swapOptimizerMemo(next: ?*OptimizerMemo) ?*OptimizerMemo {
	const previous = active_optimizer_memo;
	active_optimizer_memo = next;
	return previous;
}

pub fn encoder() encoding.Builder {
	return .{ .floor = min_dist_codes, .extra_seeds = cl_t24_arbitration,
		.memo = if (active_optimizer_memo) |m| &m.encoding else null };
}

fn buildCl(a: std.mem.Allocator, ll: []const u8, dist: []const u8) !encoding.BuiltCl {
	return encoder().header(a, ll, dist, .full);
}
fn buildClCrossing(a: std.mem.Allocator, ll: []const u8, dist: []const u8) !encoding.BuiltCl {
	return encoder().header(a, ll, dist, .crossing);
}
fn emptyDistCl(a: std.mem.Allocator, ll: []const u8, mode: encoding.Header) !encoding.DistanceHeader {
	return encoder().empty(a, ll, mode);
}
fn dynCostFromFreqs(a: std.mem.Allocator, ll: []const u32, dist: []const u32, extra: i64, mode: encoding.Header) !i64 {
	return encoder().costFromFreqs(a, ll, dist, extra, mode);
}

const ClCost = struct { header_bits: i64, cl_lengths: [19]u8 };

/// Run the full CL builder in resettable scratch and retain only costs
/// and CL lengths. Callers that do not emit entries need no retained allocation.
fn buildClCost(scratch: *std.heap.ArenaAllocator, ll_lengths: []const u8, dist_lengths: []const u8) !ClCost {
	defer _ = scratch.reset(SCRATCH_RESET);
	const built = try buildCl(scratch.allocator(), ll_lengths, dist_lengths);
	return .{ .header_bits = built.header_bits, .cl_lengths = built.cl_lengths };
}

fn fixedCost(tokens: []const Token, preserve_encoding: bool) i64 {
	var bits: i64 = 3 + fixed_ll_bits[common.EOB];
	for (tokens) |tok| {
		switch (tok) {
			.lit => |b| bits += fixed_ll_bits[b],
			.match => |m| {
				const lc = if (preserve_encoding and m.original_alt258 and m.length == common.MAX_MATCH_LENGTH)
					lenCodeTable[common.MAX_MATCH_LENGTH - 1] // symbol 284 + five extra bits
				else lenCodeTable[m.length];
				const dc = distCodeTable[m.distance];
				bits += @as(i64, fixed_ll_bits[lc.code]) + lc.extra + 5 + dc.extra;
			},
		}
	}
	return bits;
}

/// Fixed-Huffman cost of a fully-literal block. raw_freq[b] = count of byte b.
fn fixAllLitsCost(raw_freq: []const u32) i64 {
	var bits: i64 = 3 + fixed_ll_bits[common.EOB];
	for (raw_freq, 0..) |c, b| {
		if (c > 0) bits += @as(i64, c) * fixed_ll_bits[b];
	}
	return bits;
}

// Encoding context belongs to costing, not to the decoded byte program.
// Scopes restore this even when a block search fails; standalone callers start
// at offset zero. Pure Huffman portfolios do not depend on this value.
threadlocal var block_offset: u3 = 0;

fn storedRegionCost(size: usize, offset: u3) i64 {
	const padding: usize = (8 - ((@as(usize, offset) + 3) & 7)) & 7;
	const extra_chunks = if (size == 0) 0 else (size - 1) / 65535;
	return @intCast(35 + padding + 8 * size + 40 * extra_chunks);
}

fn storedCost(raw: []const u8) i64 {
	// The block search retains physical blocks. Large raw regions are lowered
	// by the stream emitter, then their new boundaries get ordinary search.
	if (raw.len > 65535) return std.math.maxInt(i64);
	return storedRegionCost(raw.len, block_offset);
}

// ── match precompute ───────────────────────

const ByteCount = struct { byte: u16, count: u32 };

const MatchInfo = struct {
	tok_index: usize,
	lits: []const u8,
	lc: u16, // length code 257..285
	xn: u3,
	dc: u16, // distance code 0..29
	dn: u4,
	hist: []const ByteCount,
};

const Precomp = struct {
	tokens: []const Token,
	matches: []const MatchInfo,
	base_ll_freq: [286]u32,
	raw: []const u8,
};

fn precomputeMatchLits(alloc: std.mem.Allocator, tokens: []const Token, program: ir.Program) !Precomp {
	var nmatches: usize = 0;
	for (tokens) |tok| if (tok == .match) { nmatches += 1; };
	var pos: usize = 0;

	const matches = try alloc.alloc(MatchInfo, nmatches);
	var mi: usize = 0;
	var base_ll_freq = [_]u32{0} ** 286;

	// Reuse a histogram that the emit pass clears as it visits entries.
	// Per-match work is proportional to match length, not alphabet size.
	var cnt = [_]u32{0} ** 256;

	for (tokens, 0..) |tok, i| {
		if (!program.accepts(pos, tok)) @panic("candidate instruction changed program output");
		switch (tok) {
			.lit => |b| {
				pos += 1;
				base_ll_freq[b] += 1;
			},
			.match => |m| {
				const dist = m.distance;
				const length = m.length;
				const lits = (ir.Span{ .start = pos, .length = length }).bytes(program);
				pos += length;

				// Sparse histogram in first-appearance order (order is
				// irrelevant downstream: every consumer sums over it). Track
				// the distinct bytes while counting so matched output is
				// scanned once, not once to count and again to discover the
				// first occurrence of each byte.
				var byte_buf: [256]u8 = undefined;
				var nhist: usize = 0;
				for (lits) |b| {
					if (cnt[b] == 0) {
						byte_buf[nhist] = b;
						nhist += 1;
					}
					cnt[b] += 1;
				}
				var hist_buf: [256]ByteCount = undefined;
				for (byte_buf[0..nhist], 0..) |b, j| {
					hist_buf[j] = .{ .byte = b, .count = cnt[b] };
					cnt[b] = 0; // re-zero for the next match
				}
				const hist = try alloc.dupe(ByteCount, hist_buf[0..nhist]);
				matches[mi] = .{
					.tok_index = i,
					.lits = lits,
					.lc = lenCodeTable[length].code,
					.xn = lenCodeTable[length].extra,
					.dc = distCodeTable[dist].code,
					.dn = distCodeTable[dist].extra,
					.hist = hist,
				};
				mi += 1;
			},
		}
	}
	if (pos != program.raw().len) @panic("candidate changed program length");
	std.debug.assert(mi == nmatches);
	if (base_ll_freq[common.EOB] == 0) base_ll_freq[common.EOB] = 1;
	return .{
		.tokens = tokens,
		.matches = matches,
		.base_ll_freq = base_ll_freq,
		.raw = program.raw(),
	};
}

// ── per-type optimizers ─────────────────────────────────────────────────────

fn applyExpansions(
	alloc: std.mem.Allocator,
	orig_tokens: []const Token,
	matches: []const MatchInfo,
	expanded: []const bool,
) ![]Token {
	// Exact output size: each expanded match trades 1 token for m.length lits.
	var total: usize = orig_tokens.len;
	for (matches, 0..) |mi, k| {
		if (expanded[k]) total += mi.lits.len - 1;
	}
	var out: std.ArrayList(Token) = .empty;
	try out.ensureTotalCapacity(alloc, total);
	var m: usize = 0;
	for (orig_tokens, 0..) |tok, i| {
		if (m < matches.len and matches[m].tok_index == i) {
			if (expanded[m]) {
				for (matches[m].lits) |b| out.appendAssumeCapacity(.{ .lit = b });
			} else {
				out.appendAssumeCapacity(tok);
			}
			m += 1;
		} else {
			out.appendAssumeCapacity(tok);
		}
	}
	std.debug.assert(out.items.len == total);
	return out.items;
}

const FixedResult = struct { tokens: []Token, cost: i64 };

fn optFixed(alloc: std.mem.Allocator, orig_tokens: []const Token, matches: []const MatchInfo) !FixedResult {
	var out: std.ArrayList(Token) = .empty;
	var bits: i64 = 3 + fixed_ll_bits[common.EOB];
	var m: usize = 0;
	for (orig_tokens, 0..) |tok, i| {
		if (m < matches.len and matches[m].tok_index == i) {
			const mi = matches[m];
			m += 1;
			const mc: i64 = @as(i64, fixed_ll_bits[mi.lc]) + mi.xn + 5 + mi.dn;
			var lc_cost: i64 = 0;
			for (mi.lits) |b| lc_cost += fixed_ll_bits[b];
			if (lc_cost <= mc) {
				for (mi.lits) |b| try out.append(alloc, .{ .lit = b });
				bits += lc_cost;
			} else {
				try out.append(alloc, tok);
				bits += mc;
			}
		} else {
			try out.append(alloc, tok);
			bits += fixed_ll_bits[tok.lit];
		}
	}
	return .{ .tokens = out.items, .cost = bits };
}

fn expandMatch(ll_freq: []u32, dist_freq: []u32, kept_extra: *i64, mi: MatchInfo, drop_258: bool) void {
	if (drop_258 and mi.lc == 285) {
		// length-258 with symbol 285 omitted lives at 284 (+5 extra), not 285.
		ll_freq[284] -= 1;
		kept_extra.* -= 5 + @as(i64, mi.dn);
	} else {
		ll_freq[mi.lc] -= 1;
		kept_extra.* -= @as(i64, mi.xn) + @as(i64, mi.dn);
	}
	dist_freq[mi.dc] -= 1;
	for (mi.hist) |hc| ll_freq[hc.byte] += hc.count;
}

// Prices are frozen for a whole round, even as its frequency counts change.
const ExpansionPrices = struct { ll: [286]u8, dist: [30]u8 };
fn expansionPrices(ll_freq: *const [286]u32, dist_freq: *const [30]u32) ExpansionPrices {
	var prices: ExpansionPrices = .{ .ll = undefined, .dist = @splat(0) };
	freqToLengths(ll_freq, 15, &prices.ll);
	var any_dist = false;
	for (dist_freq) |f| if (f > 0) { any_dist = true; };
	if (any_dist) {
		freqToLengths(dist_freq, 15, &prices.dist);
		distFloor(&prices.dist);
	}
	// These are generated trees; encoding supplied trees still validates them.
	std.debug.assert(common.HuffEnc(288).build(&prices.ll) != null);
	std.debug.assert(common.HuffEnc(32).build(&prices.dist) != null);
	for (&prices.ll) |*l| if (l.* == 0) { l.* = 15; };
	for (&prices.dist) |*l| if (l.* == 0) { l.* = 15; };
	return prices;
}

const NearTie = struct { idx: usize, delta: i64 };

fn optDynamic(
	alloc: std.mem.Allocator,
	orig_tokens: []const Token,
	matches: []const MatchInfo,
	base_ll_freq: [286]u32,
	drop_258: bool,
	cl_model: ClModel,
) ![]Token {
	const expanded = try alloc.alloc(bool, matches.len);
	@memset(expanded, false);

	// Reset temporary Huffman and CL-builder allocations after each cost
	// evaluation. Branch-and-bound can evaluate up to 2^8 subsets per round.
	var cost_scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer cost_scratch.deinit();

	var ll_freq: [286]u32 = base_ll_freq;
	var dist_freq = [_]u32{0} ** 30;
	var kept_extra: i64 = 0;
	for (matches) |mi| {
		if (drop_258 and mi.lc == 285) {
			// With symbol 285 omitted, length-258 routes through 284+5+31, not 285.
			ll_freq[284] += 1;
			kept_extra += 5 + @as(i64, mi.dn);
		} else {
			ll_freq[mi.lc] += 1;
			kept_extra += @as(i64, mi.xn) + @as(i64, mi.dn);
		}
		dist_freq[mi.dc] += 1;
	}
	if (drop_258) ll_freq[285] = 0; // never let 285 enter the table

	while (true) {
		const prices = expansionPrices(&ll_freq, &dist_freq);
		var greedy = false;
		var near_ties: std.ArrayList(NearTie) = .empty;

		for (matches, 0..) |mi, idx| {
			if (expanded[idx]) continue;
			var ll_b: i64 = undefined;
			var m_extra: i64 = undefined;
			if (drop_258 and mi.lc == 285) {
				ll_b = prices.ll[284];
				m_extra = 5;
			} else {
				ll_b = prices.ll[mi.lc];
				m_extra = mi.xn;
			}
			const d_b: i64 = prices.dist[mi.dc];
			const mc: i64 = ll_b + m_extra + d_b + mi.dn;
			var lc_cost: i64 = 0;
			for (mi.hist) |hc| lc_cost += @as(i64, hc.count) * prices.ll[hc.byte];
			const delta = mc - lc_cost;
			if (delta > TIE_THRESHOLD) {
				expandMatch(&ll_freq, &dist_freq, &kept_extra, mi, drop_258);
				expanded[idx] = true;
				greedy = true;
			} else if (delta >= -TIE_THRESHOLD) {
				try near_ties.append(alloc, .{ .idx = idx, .delta = delta });
			}
		}

		if (greedy) continue;
		if (near_ties.items.len == 0) break;

		if (near_ties.items.len > MAX_NEAR_TIES) {
			var any = false;
			for (near_ties.items) |nt| {
				if (nt.delta >= 0) {
					expandMatch(&ll_freq, &dist_freq, &kept_extra, matches[nt.idx], drop_258);
					expanded[nt.idx] = true;
					any = true;
				}
			}
			if (any) continue;
			break;
		}

		// Branch & bound over 2^k near-tie subsets (first strictly-better wins).
		const k = near_ties.items.len;
		// Use greedy CL costs during search. Their overestimates can drive the
		// expansion loop past states where the exact-cost search stops. The
		// selected encoding is always costed exactly before acceptance.
		const baseline = try dynCostFromFreqs(cost_scratch.allocator(), &ll_freq, &dist_freq, kept_extra, cl_model);
		_ = cost_scratch.reset(SCRATCH_RESET);
		var best_cost = baseline;
		var best_mask: usize = 0;
		var mask: usize = 1;
		while (mask < (@as(usize, 1) << @intCast(k))) : (mask += 1) {
			var ll_f: [286]u32 = ll_freq;
			var dist_f: [30]u32 = dist_freq;
			var extra = kept_extra;
			var j: usize = 0;
			while (j < k) : (j += 1) {
				if ((mask >> @intCast(j)) & 1 == 1) {
					expandMatch(&ll_f, &dist_f, &extra, matches[near_ties.items[j].idx], drop_258);
				}
			}
			const cost = try dynCostFromFreqs(cost_scratch.allocator(), &ll_f, &dist_f, extra, cl_model);
			_ = cost_scratch.reset(SCRATCH_RESET);
			if (cost < best_cost) {
				best_cost = cost;
				best_mask = mask;
			}
		}
		if (best_mask != 0) {
			var j: usize = 0;
			while (j < k) : (j += 1) {
				if ((best_mask >> @intCast(j)) & 1 == 1) {
					const idx = near_ties.items[j].idx;
					expandMatch(&ll_freq, &dist_freq, &kept_extra, matches[idx], drop_258);
					expanded[idx] = true;
				}
			}
			continue;
		}
		break;
	}

	return applyExpansions(alloc, orig_tokens, matches, expanded);
}

const BIDIR_MAX_ROUNDS = 100;

// Bidirectional batch greedy: optDynamic's
// greedy loop with an UN-EXPAND direction, no tie window, no B&B, no drop-258
// routing. Monotone batch expansion can overshoot (all deltas priced under
// the pre-batch tree); here every match is re-priced each round and moved
// strictly-profitably in either direction, bounded by BIDIR_MAX_ROUNDS
// to stop oscillation. One more candidate stream
// for optimizeBlock's exact compare.
fn optDynamicBidir(
	alloc: std.mem.Allocator,
	orig_tokens: []const Token,
	matches: []const MatchInfo,
	base_ll_freq: [286]u32,
) ![]Token {
	const expanded = try alloc.alloc(bool, matches.len);
	@memset(expanded, false);

	var ll_freq: [286]u32 = base_ll_freq;
	var dist_freq = [_]u32{0} ** 30;
	for (matches) |mi| {
		ll_freq[mi.lc] += 1;
		dist_freq[mi.dc] += 1;
	}

	var round: usize = 0;
	while (round < BIDIR_MAX_ROUNDS) : (round += 1) {
		const prices = expansionPrices(&ll_freq, &dist_freq);
		var changed = false;
		for (matches, 0..) |mi, idx| {
			const ll_b: i64 = prices.ll[mi.lc];
			const d_b: i64 = prices.dist[mi.dc];
			const mc: i64 = ll_b + mi.xn + d_b + mi.dn;
			var lc_cost: i64 = 0;
			for (mi.hist) |hc| lc_cost += @as(i64, hc.count) * prices.ll[hc.byte];
			if (expanded[idx]) {
				if (mc >= lc_cost) continue;
				ll_freq[mi.lc] += 1;
				dist_freq[mi.dc] += 1;
				for (mi.hist) |hc| ll_freq[hc.byte] -= hc.count;
			} else {
				if (lc_cost >= mc) continue;
				ll_freq[mi.lc] -= 1;
				dist_freq[mi.dc] -= 1;
				for (mi.hist) |hc| ll_freq[hc.byte] += hc.count;
			}
			expanded[idx] = !expanded[idx];
			changed = true;
		}
		if (!changed) break;
	}
	return applyExpansions(alloc, orig_tokens, matches, expanded);
}

// Block optimization

// Payload-tied tree polishing: deterministic first-improvement moves
// (pairwise swaps and same-depth triples) preserving the Kraft sum.
// Screen with incremental greedy-RLE costs, confirm with the exact RLE DP
// under the same CL tree, and snapshot each sweep under buildCl.

const POLISH_MAX_SWEEPS = 12;
const POLISH_TRIPLE_SYMS = 12;
const POLISH_TRIPLE_CAP = 400;
const POLISH_PROMOTE_CANDS = 8;
const POLISH_DEMOTE_SYMS = 24;
const KRAFT_FULL: i64 = 1 << 15; // Kraft sum of a complete code, 2^-15 units

fn polishClCosts(cl_lengths: *const [19]u8) ![19]i64 {
	const enc = common.HuffEnc(19).build(cl_lengths) orelse return error.Malformed;
	var clc: [19]i64 = undefined;
	// A CL symbol absent from the sweep tree prices at 8 bits (pessimistic;
	// max real CL code is 7) — the middle oracle still arbitrates.
	for (0..19) |s| clc[s] = if (enc.len[s] != 0) enc.len[s] else 8;
	return clc;
}

/// Screen price of one maximal run (value v, count c), chunked exactly as
/// genClEntries chunks it (zeros: greedy rep18/rep17/lit; non-zeros: the
/// lit + rep16(<=6) cycle).
fn polishRunBits(v: u8, count: u32, clc: *const [19]i64) i64 {
	var bits: i64 = 0;
	var c: i64 = count;
	if (v == 0) {
		const l0 = clc[0];
		const r17 = clc[17] + 3;
		const r18 = clc[18] + 7;
		while (c > 0) {
			if (c >= 11) {
				bits += r18;
				c -= @min(c, 138);
			} else if (c >= 3) {
				bits += r17;
				c = 0;
			} else {
				bits += l0;
				c -= 1;
			}
		}
	} else {
		// Closed form of the lit + rep16(<=6) cycle loop (hot in the polish
		// screen): c >= 7 consumes exactly 7 per (lit, rep16) cycle; a tail of
		// 4..6 is one final (lit, rep16); a tail of 1..3 is bare lits.
		const lv = clc[v];
		const r16 = clc[16] + 2;
		const q = @divTrunc(c, 7);
		const rem = @mod(c, 7);
		bits += q * (lv + r16);
		bits += if (rem >= 4) lv + r16 else rem * lv;
	}
	return bits;
}

/// Run-list section state: maximal equal-value runs, position -> run index,
/// prefix sums of per-run screen prices. Buffers are caller-owned and sized
/// for the section; polishBuild refills them in place after each accept.
const PolishState = struct {
	rv: []u8,
	rs: []u16,
	rc: []u16,
	nr: usize,
	pos2run: []u16,
	prefix: []i64,
};

const PolishBuffers = struct {
	rv: [MAX_CL_SEQ]u8,
	rs: [MAX_CL_SEQ]u16,
	rc: [MAX_CL_SEQ]u16,
	pos2run: [MAX_CL_SEQ]u16,
	prefix: [MAX_CL_SEQ + 1]i64,

	fn state(self: *PolishBuffers, n: usize) PolishState {
		return .{ .rv = self.rv[0..n], .rs = self.rs[0..n], .rc = self.rc[0..n], .nr = 0,
			.pos2run = self.pos2run[0..n], .prefix = self.prefix[0 .. n + 1] };
	}
};

fn polishBuild(st: *PolishState, seq: []const u8, clc: *const [19]i64) void {
	var nr: usize = 0;
	var i: usize = 0;
	const n = seq.len;
	while (i < n) {
		const v = seq[i];
		var j = i + 1;
		while (j < n and seq[j] == v) j += 1;
		st.rv[nr] = v;
		st.rs[nr] = @intCast(i);
		st.rc[nr] = @intCast(j - i);
		var p = i;
		while (p < j) : (p += 1) st.pos2run[p] = @intCast(nr);
		nr += 1;
		i = j;
	}
	st.nr = nr;
	st.prefix[0] = 0;
	for (0..nr) |r| st.prefix[r + 1] = st.prefix[r] + polishRunBits(st.rv[r], st.rc[r], clc);
}

/// Screen delta of seq[p] = w, priced inside the run-closed window
/// [rp-1, rp+1] (exact for a single-site change — see unflate).
fn polishSiteDelta(st: *const PolishState, p: usize, w: u8, clc: *const [19]i64) i64 {
	const rp: usize = st.pos2run[p];
	const r0 = if (rp > 0) rp - 1 else rp;
	const r1 = if (rp + 1 < st.nr) rp + 1 else rp;
	const old = st.prefix[r1 + 1] - st.prefix[r0];
	var sv: [5]u8 = undefined;
	var sc: [5]u32 = undefined;
	var ns: usize = 0;
	var ri = r0;
	while (ri <= r1) : (ri += 1) {
		if (ri == rp) {
			const k: u32 = @intCast(p - st.rs[rp]);
			if (k > 0) {
				sv[ns] = st.rv[rp];
				sc[ns] = k;
				ns += 1;
			}
			sv[ns] = w;
			sc[ns] = 1;
			ns += 1;
			const rest = st.rc[rp] - k - 1;
			if (rest > 0) {
				sv[ns] = st.rv[rp];
				sc[ns] = rest;
				ns += 1;
			}
		} else {
			sv[ns] = st.rv[ri];
			sc[ns] = st.rc[ri];
			ns += 1;
		}
	}
	var new: i64 = 0;
	var mv = sv[0];
	var mc = sc[0];
	for (1..ns) |q| {
		if (sv[q] == mv) {
			mc += sc[q];
		} else {
			new += polishRunBits(mv, mc, clc);
			mv = sv[q];
			mc = sc[q];
		}
	}
	new += polishRunBits(mv, mc, clc);
	return new - old;
}

const PolishWin = struct { lo: usize, hi: usize };

/// Run-boundary-closed window around position p.
fn polishWindow(seq: []const u8, p: usize) PolishWin {
	const n = seq.len;
	var lo = p;
	if (lo > 0) {
		lo -= 1;
		while (lo > 0 and seq[lo - 1] == seq[lo]) lo -= 1;
	}
	var hi = p;
	if (hi < n - 1) {
		hi += 1;
		while (hi < n - 1 and seq[hi + 1] == seq[hi]) hi += 1;
	}
	return .{ .lo = lo, .hi = hi + 1 };
}

/// Sort by lo and merge overlapping or touching windows; at most 3 inputs.
fn polishMergeWins(wins: []PolishWin) usize {
	// insertion sort (tiny, deterministic)
	var i: usize = 1;
	while (i < wins.len) : (i += 1) {
		const w = wins[i];
		var j = i;
		while (j > 0 and (wins[j - 1].lo > w.lo or
				(wins[j - 1].lo == w.lo and wins[j - 1].hi > w.hi))) : (j -= 1) {
			wins[j] = wins[j - 1];
		}
		wins[j] = w;
	}
	var out: usize = 1;
	for (1..wins.len) |q| {
		if (wins[q].lo <= wins[out - 1].hi) {
			if (wins[q].hi > wins[out - 1].hi) wins[out - 1].hi = wins[q].hi;
		} else {
			wins[out] = wins[q];
			out += 1;
		}
	}
	return out;
}

fn polishPriceWins(seq: []const u8, wins: []const PolishWin, clc: *const [19]i64) i64 {
	var bits: i64 = 0;
	for (wins) |w| {
		var i = w.lo;
		while (i < w.hi) {
			const v = seq[i];
			var j = i + 1;
			while (j < w.hi and seq[j] == v) j += 1;
			bits += polishRunBits(v, @intCast(j - i), clc);
			i = j;
		}
	}
	return bits;
}

/// Direct window-priced screen delta for multi-site moves. Restores seq.
fn polishSpanDelta(seq: []u8, positions: []const usize, newvals: []const u8, clc: *const [19]i64) i64 {
	var winbuf: [3]PolishWin = undefined;
	for (positions, 0..) |p, q| winbuf[q] = polishWindow(seq, p);
	const nw = polishMergeWins(winbuf[0..positions.len]);
	const wins = winbuf[0..nw];
	var saved: [3]u8 = undefined;
	for (positions, 0..) |p, q| saved[q] = seq[p];
	const old = polishPriceWins(seq, wins, clc);
	for (positions, newvals) |p, w| seq[p] = w;
	const new = polishPriceWins(seq, wins, clc);
	for (positions, 0..) |p, q| seq[p] = saved[q];
	return new - old;
}

const PolishRunWin = struct { r0: usize, r1: usize };

fn polishAppendRun(sv: *[16]u8, sc: *[16]u32, ns: *usize, v: u8, count: usize) void {
	if (count == 0) return;
	if (ns.* > 0 and sv[ns.* - 1] == v) {
		sc[ns.* - 1] += @intCast(count);
	} else {
		std.debug.assert(ns.* < sv.len);
		sv[ns.*] = v;
		sc[ns.*] = @intCast(count);
		ns.* += 1;
	}
}

/// Run-state version of polishSpanDelta for pair/triple moves. Reuse known
/// maximal-run boundaries and prices instead of rescanning each candidate.
/// Windows use inclusive run-index ranges rather than byte offsets.
fn polishSpanDeltaState(
		st: *const PolishState,
		positions: []const usize,
		newvals: []const u8,
		clc: *const [19]i64,
		comptime exact: bool,
) i64 {
	std.debug.assert(positions.len > 0 and positions.len <= 3 and positions.len == newvals.len);
	var order = [_]usize{ 0, 1, 2 };
	var q: usize = 1;
	while (q < positions.len) : (q += 1) {
		const x = order[q];
		var j = q;
		while (j > 0 and positions[order[j - 1]] > positions[x]) : (j -= 1)
			order[j] = order[j - 1];
		order[j] = x;
	}

	var winbuf: [3]PolishRunWin = undefined;
	for (positions, 0..) |p, k| {
		winbuf[k] = .{
			.r0 = st.pos2run[if (p > 0) p - 1 else p],
			.r1 = st.pos2run[if (p + 1 < st.pos2run.len) p + 1 else p],
		};
	}
	// Insertion sort + merge, matching polishMergeWins. Adjacent run ranges
	// represent byte windows whose exclusive/inclusive boundaries touch.
	q = 1;
	while (q < positions.len) : (q += 1) {
		const w = winbuf[q];
		var j = q;
		while (j > 0 and (winbuf[j - 1].r0 > w.r0 or
				(winbuf[j - 1].r0 == w.r0 and winbuf[j - 1].r1 > w.r1))) : (j -= 1) {
			winbuf[j] = winbuf[j - 1];
		}
		winbuf[j] = w;
	}
	var nw: usize = 1;
	for (1..positions.len) |k| {
		if (winbuf[k].r0 <= winbuf[nw - 1].r1 + 1) {
			winbuf[nw - 1].r1 = @max(winbuf[nw - 1].r1, winbuf[k].r1);
		} else {
			winbuf[nw] = winbuf[k];
			nw += 1;
		}
	}

	var delta: i64 = 0;
	for (winbuf[0..nw]) |w| {
		var old: i64 = if (exact) 0 else st.prefix[w.r1 + 1] - st.prefix[w.r0];
		if (exact) for (w.r0..w.r1 + 1) |r| {
			old += polishExactRunBits(st.rv[r], st.rc[r], clc);
		};
		// Three merged 3-run neighborhoods contain at most 9 original runs;
		// splitting at three changed sites adds at most 6 fragments.
		var sv: [16]u8 = undefined;
		var sc: [16]u32 = undefined;
		var ns: usize = 0;
		var oi: usize = 0;
		for (w.r0..w.r1 + 1) |r| {
			const start: usize = st.rs[r];
			const end = start + st.rc[r];
			var at = start;
			while (oi < positions.len and positions[order[oi]] < start) oi += 1;
			while (oi < positions.len and positions[order[oi]] < end) : (oi += 1) {
				const mi = order[oi];
				const p = positions[mi];
				polishAppendRun(&sv, &sc, &ns, st.rv[r], p - at);
				polishAppendRun(&sv, &sc, &ns, newvals[mi], 1);
				at = p + 1;
			}
			polishAppendRun(&sv, &sc, &ns, st.rv[r], end - at);
		}
		var new: i64 = 0;
		for (sv[0..ns], sc[0..ns]) |v, count| new += if (exact) polishExactRunBits(v, count, clc) else polishRunBits(v, count, clc);
		delta += new - old;
	}
	return delta;
}

/// Middle oracle: cost-only twin of dpClSection under fixed CL costs clc
/// (missing symbols already priced 8 by polishClCosts — NOT CL_UNUSED_COST;
/// this DP is the polish's internal guide, not a materialization).
fn polishDpCostReference(seq: []const u8, clc: *const [19]i64, f: []i64) i64 {
	const c16 = clc[16] + 2;
	const c17 = clc[17] + 3;
	const c18 = clc[18] + 7;
	const n = seq.len;
	f[0] = 0;
	var run: u32 = 0;
	var zrun: u32 = 0;
	var prev: i32 = -1;
	// rep18 sliding-window minimum, same construction as dpClSection's (see
	// the comment there). Cost-only here, so even tie behavior is moot — only
	// the min matters.
	var dq: [MAX_CL_SEQ + 1]u32 = undefined;
	var dq_head: usize = 0;
	var dq_tail: usize = 0;
	for (1..n + 1) |i| {
		const v = seq[i - 1];
		run = if (v == prev) run + 1 else 1;
		zrun = if (v == 0) zrun + 1 else 0;
		prev = v;
		if (v != 0) {
			dq_head = 0;
			dq_tail = 0;
		}
		var best = f[i - 1] + clc[v];
		const kmax16: usize = @min(6, if (run > 0) run - 1 else 0);
		var k: usize = 3;
		while (k <= kmax16) : (k += 1) {
			const c = f[i - k] + c16;
			if (c < best) best = c;
		}
		if (zrun > 0) {
			const kmax: usize = @min(10, zrun);
			k = 3;
			while (k <= kmax) : (k += 1) {
				const c = f[i - k] + c17;
				if (c < best) best = c;
			}
			if (zrun >= 11) {
				const j_new: u32 = @intCast(i - 11);
				while (dq_tail > dq_head and f[dq[dq_tail - 1]] >= f[j_new]) dq_tail -= 1;
				dq[dq_tail] = j_new;
				dq_tail += 1;
				const j_lo = i - @min(138, zrun);
				while (dq[dq_head] < j_lo) dq_head += 1;
				const c = f[dq[dq_head]] + c18;
				if (c < best) best = c;
			}
		}
		f[i] = best;
	}
	return f[n];
}

/// Exact fixed-price DP cost factored over maximal equal-value runs. No
/// repeat can cross a run boundary, and rep16 requires a preceding value
/// inside its run. Thus each run's optimum is independent. This changes
/// only the middle oracle's implementation, not screening or move order.
fn polishDpCost(seq: []const u8, clc: *const [19]i64) i64 {
	std.debug.assert(seq.len <= MAX_CL_SEQ);
	for (clc) |price| std.debug.assert(price >= 1 and price <= 8);
	
	var total: i64 = 0;
	var i: usize = 0;
	while (i < seq.len) {
		const v = seq[i];
		var j = i + 1;
		while (j < seq.len and seq[j] == v) j += 1;
		total += encoding.runCosts(v, clc)[j - i];
		i = j;
	}
	return total;
}

fn polishExactRunBits(v: u8, count: u32, clc: *const [19]i64) i64 {
	return encoding.runCosts(v, clc)[count];
}

test "polish run costs: exhaustive prices and short sequences match DP" {
	var seq: [MAX_CL_SEQ]u8 = undefined;
	var reference: [MAX_CL_SEQ + 1]i64 = undefined;
	var clc = [_]i64{1} ** 19;
	// All 4096 legal zero-run price combinations, every run length at once.
	@memset(&seq, 0);
	for (1..9) |literal| for (1..9) |r16| for (1..9) |r17| for (1..9) |r18| {
		clc[0] = @intCast(literal);
		clc[16] = @intCast(r16);
		clc[17] = @intCast(r17);
		clc[18] = @intCast(r18);
		_ = polishDpCostReference(&seq, &clc, &reference);
		const costs = encoding.runCosts(0, &clc);
		for (reference, costs) |want, got| try std.testing.expectEqual(want, @as(i64, got));
	};
	// All nonzero literal/repeat price pairs, including rep16's mandatory
	// preceding value and boundaries 3/6/7. Prices are 1..8 (missing = 8).
	@memset(&seq, 1);
	for (1..9) |literal| for (1..9) |r16| {
		clc[1] = @intCast(literal);
		clc[16] = @intCast(r16);
		_ = polishDpCostReference(&seq, &clc, &reference);
		for (reference, encoding.runCosts(1, &clc)) |want, got| try std.testing.expectEqual(want, @as(i64, got));
	};
	// Exhaustive ternary sequences through length 8 exercise run boundaries,
	// with independent varying prices for zeros and both nonzero values.
	for (0..8) |profile| {
		for (&clc, 0..) |*v, i| v.* = @intCast(1 + (i * 3 + profile * (i + 1)) % 8);
		var count: usize = 1;
		for (0..9) |len| {
			for (0..count) |code| {
				var rest = code;
				for (seq[0..len]) |*v| { v.* = @intCast(rest % 3); rest /= 3; }
				try std.testing.expectEqual(polishDpCostReference(seq[0..len], &clc, &reference), polishDpCost(seq[0..len], &clc));
			}
			count *= 3;
		}
	}
}

test "polish run costs: local deltas match whole-sequence oracles" {
	var rng = std.Random.DefaultPrng.init(0x70c0a57);
	const random = rng.random();
	var buf: [MAX_CL_SEQ]u8 = undefined;
	var f: [MAX_CL_SEQ + 1]i64 = undefined;
	var buffers: PolishBuffers = undefined;
	for (0..2000) |trial| {
		const n = random.intRangeAtMost(usize, 3, MAX_CL_SEQ);
		const seq = buf[0..n];
		var clc: [19]i64 = undefined;
		for (&clc) |*v| v.* = random.intRangeAtMost(i64, 1, 8);
		// Alternate many short runs with long zero/nonzero runs.
		var i: usize = 0;
		while (i < n) {
			const end = @min(n, i + random.intRangeAtMost(usize, 1, if (trial % 2 == 0) 4 else 160));
			@memset(seq[i..end], random.intRangeAtMost(u8, 0, 15));
			i = end;
		}
		var st = buffers.state(n);
		polishBuild(&st, seq, &clc);
		for (1..4) |count| {
			var ps: [3]usize = undefined;
			var values: [3]u8 = undefined;
			for (0..count) |k| {
				while (true) {
					ps[k] = random.intRangeLessThan(usize, 0, n);
					if (std.mem.indexOfScalar(usize, ps[0..k], ps[k]) == null) break;
				}
				values[k] = random.intRangeAtMost(u8, 0, 15);
			}
			const positions = ps[0..count];
			const newvals = values[0..count];
			try std.testing.expectEqual(polishSpanDelta(seq, positions, newvals, &clc), polishSpanDeltaState(&st, positions, newvals, &clc, false));
			const old = polishDpCostReference(seq, &clc, &f);
			const delta = polishSpanDeltaState(&st, positions, newvals, &clc, true);
			for (positions, newvals) |p, v| seq[p] = v;
			try std.testing.expectEqual(polishDpCostReference(seq, &clc, &f) - old, delta);
			polishBuild(&st, seq, &clc);
		}
	}
}

const PolishPassResult = struct { dp: i64, improved: bool };

test "sweep memo preserves moves, complete keys, collisions and ownership" {
	var memo = try OptimizerMemo.init(std.testing.allocator, 1);
	defer memo.deinit();
	const previous = swapOptimizerMemo(&memo);
	defer _ = swapOptimizerMemo(previous);
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	var prng = std.Random.DefaultPrng.init(0x737765657073);
	const random = prng.random();
	var saw_change = false;
	for (0..160) |trial| {
		_ = arena.reset(.retain_capacity);
		const a = arena.allocator();
		const n = 16 + trial % 81;
		var freqs: [96]u32 = undefined;
		for (freqs[0..n]) |*f| f.* = random.intRangeAtMost(u32, 0, 12);
		var input: [96]u8 = undefined;
		freqToLengths(freqs[0..n], 15, input[0..n]);
		// A permutation preserves Kraft equality while creating useful swaps.
		random.shuffle(u8, input[0..n]);
		// Uncoded symbols have no emissions, as in a materialized candidate.
		for (input[0..n], freqs[0..n]) |len, *f| if (len == 0) { f.* = 0; };
		var prices: [19]i64 = undefined;
		for (&prices) |*p| p.* = random.intRangeAtMost(i64, 1, 8);
		for ([_]bool{ false, true }) |structural| {
			const cap = if (trial % 2 == 0) n else n / 2;
			var expected = input;
			const result = if (structural)
				polishStructuralPassUncached(expected[0..n], freqs[0..n], &prices, cap, 0)
			else
				try polishSectionPassUncached(a, expected[0..n], freqs[0..n], &prices);
			saw_change = saw_change or result.improved;
			var actual = input;
			const misses = memo.sweep_misses;
			const measured = if (structural)
				polishStructuralPass(actual[0..n], freqs[0..n], &prices, cap, 0)
			else
				try polishSectionPass(a, actual[0..n], freqs[0..n], &prices);
			try std.testing.expectEqual(misses + 1, memo.sweep_misses);
			try std.testing.expectEqualDeep(result, measured);
			try std.testing.expectEqualSlices(u8, expected[0..n], actual[0..n]);
			// Mutate a returned state, then replay the original request. The
			// caller owns its state; the stored continuation must be unaffected.
			@memset(actual[0..n], 0);
			actual = input;
			const hits = memo.sweep_hits;
			const cached = if (structural)
				polishStructuralPass(actual[0..n], freqs[0..n], &prices, cap, 0)
			else
				try polishSectionPass(a, actual[0..n], freqs[0..n], &prices);
			try std.testing.expectEqual(hits + 1, memo.sweep_hits);
			try std.testing.expectEqualDeep(result, cached);
			try std.testing.expectEqualSlices(u8, expected[0..n], actual[0..n]);
		}
	}
	try std.testing.expect(saw_change);
	// Deliberately force every key into one slot and independently change
	// each dependency, even those that might leave the measured answer tied.
	var seq = [_]u8{ 2, 2, 2, 2, 0 };
	var freqs = [_]u32{ 9, 0, 2, 1, 0 };
	var prices = [_]i64{3} ** 19;
	const slot = &memo.sweep_slots[0];
	const result: PolishPassResult = .{ .dp = 0, .improved = false };
	slot.save(.structural, &seq, &freqs, &prices, 5, 0, &seq, result);
	try std.testing.expect(slot.replay(.section, &seq, &freqs, &prices, 5, 0) == null);
	try std.testing.expect(slot.replay(.structural, &seq, &freqs, &prices, 4, 0) == null);
	try std.testing.expect(slot.replay(.structural, &seq, &freqs, &prices, 5, 2) == null);
	try std.testing.expect(slot.replay(.structural, seq[0..4], freqs[0..4], &prices, 5, 0) == null);
	seq[4] = 1;
	try std.testing.expect(slot.replay(.structural, &seq, &freqs, &prices, 5, 0) == null);
	seq[4] = 0;
	freqs[0] += 1;
	try std.testing.expect(slot.replay(.structural, &seq, &freqs, &prices, 5, 0) == null);
	freqs[0] -= 1;
	prices[18] += 1;
	try std.testing.expect(slot.replay(.structural, &seq, &freqs, &prices, 5, 0) == null);
	prices[18] -= 1;
	try std.testing.expectEqualDeep(result, slot.replay(.structural, &seq, &freqs, &prices, 5, 0).?);
}

const PolishPass = struct {
	seq: []u8,
	freqs: []const u32,
	clc: *const [19]i64,
	st: PolishState,
	s_table: []i64,
	idx: []usize,
	present: []u8,

	fn sRow(self: *PolishPass, p: usize) void {
		const base = p * 16;
		const sp = self.seq[p];
		for (self.present) |w| {
			if (w != sp) {
				self.s_table[base + w] = polishSiteDelta(&self.st, p, w, self.clc);
			}
		}
	}

	/// Middle-confirm a screen-passing move; apply + refresh on accept.
	fn tryApply(self: *PolishPass, positions: []const usize, newvals: []const u8, dp: i64) bool {
		const delta = polishSpanDeltaState(&self.st, positions, newvals, self.clc, true);
		if (delta + dp >= 0) return false;
		// Compute affected spans before the move, then rebuild run structures
		// and refresh S rows whose neighborhoods intersect those spans.
		var winbuf: [3]PolishWin = undefined;
		for (positions, 0..) |q, k| winbuf[k] = polishWindow(self.seq, q);
		const nw = polishMergeWins(winbuf[0..positions.len]);
		const spans = winbuf[0..nw];
		for (positions, newvals) |q, w| self.seq[q] = w;
		polishBuild(&self.st, self.seq, self.clc);
		for (self.idx) |p| {
			const rp: usize = self.st.pos2run[p];
			const r0 = if (rp > 0) rp - 1 else rp;
			const r1 = if (rp + 1 < self.st.nr) rp + 1 else rp;
			const lo: usize = self.st.rs[r0];
			const hi: usize = @as(usize, self.st.rs[r1]) + self.st.rc[r1];
			for (spans) |s| {
				if (lo < s.hi and s.lo < hi) {
					self.sRow(p);
					break;
				}
			}
		}
		return true;
	}
};

/// One first-improvement pass over one code-length section: all pairwise
/// swaps in ascending (i, j) order, then same-depth triples.
fn polishSectionPass(alloc: std.mem.Allocator, seq: []u8, freqs: []const u32, clc: *const [19]i64) !PolishPassResult {
	if (active_optimizer_memo) |memo| {
		if (seq.len <= 288) {
			const slot = memo.sweepSlot(.section, seq, freqs, clc, 0, 0);
			if (slot.replay(.section, seq, freqs, clc, 0, 0)) |result| {
				memo.sweep_hits += 1;
				return result;
			}
			memo.sweep_misses += 1;
			var input: [288]u8 = undefined;
			@memcpy(input[0..seq.len], seq);
			const result = try polishSectionPassUncached(alloc, seq, freqs, clc);
			slot.save(.section, input[0..seq.len], freqs, clc, 0, 0, seq, result);
			return result;
		}
	}
	return polishSectionPassUncached(alloc, seq, freqs, clc);
}

fn polishSectionPassUncached(alloc: std.mem.Allocator, seq: []u8, freqs: []const u32, clc: *const [19]i64) !PolishPassResult {
	const n = seq.len;
	var idx_buf = try alloc.alloc(usize, n);
	var ni: usize = 0;
	for (0..n) |i| {
		if (seq[i] > 0) {
			idx_buf[ni] = i;
			ni += 1;
		}
	}
	const idx = idx_buf[0..ni];
	var present_set = [_]bool{false} ** 16;
	for (idx) |i| present_set[seq[i]] = true;
	var present_buf: [16]u8 = undefined;
	var np: usize = 0;
	for (1..16) |w| {
		if (present_set[w]) {
			present_buf[np] = @intCast(w);
			np += 1;
		}
	}
	var buffers: PolishBuffers = undefined;
	var pass: PolishPass = .{
		.seq = seq,
		.freqs = freqs,
		.clc = clc,
		.st = buffers.state(n),
		.s_table = try alloc.alloc(i64, n * 16),
		.idx = idx,
		.present = present_buf[0..np],
	};
	polishBuild(&pass.st, seq, clc);
	for (idx) |p| pass.sRow(p);

	var dp_total: i64 = 0;
	var improved = false;
	// pairwise swaps, ascending (i, j)
	for (0..ni) |a| {
		const i = idx[a];
		var u = seq[i];
		const fi = pass.freqs[i];
		for (a + 1..ni) |b| {
			const j = idx[b];
			const v = seq[j];
			if (v == u) continue;
			const dp = (@as(i64, fi) - pass.freqs[j]) * (@as(i64, v) - u);
			const ri: i64 = pass.st.pos2run[i];
			const rj: i64 = pass.st.pos2run[j];
			const d = if (@abs(ri - rj) > 2)
				pass.s_table[i * 16 + v] + pass.s_table[j * 16 + u] + dp
			else
				polishSpanDeltaState(&pass.st, &.{ i, j }, &.{ v, u }, clc, false) + dp;
			if (d < 0 and pass.tryApply(&.{ i, j }, &.{ v, u }, dp)) {
				dp_total += dp;
				improved = true;
				u = seq[i];
			}
		}
	}
	// same-depth triples: x -> d-1, y,z -> d+1 (Kraft-exact)
	const Tri = struct { x: usize, y: usize, z: usize };
	var tris: [POLISH_TRIPLE_CAP]Tri = undefined;
	var nt: usize = 0;
	var depth: u8 = 2;
	outer: while (depth <= 15) : (depth += 1) {
		var syms_buf: [288]usize = undefined;
		var nsym: usize = 0;
		for (idx) |i| {
			if (seq[i] == depth) {
				syms_buf[nsym] = i;
				nsym += 1;
			}
		}
		if (nsym < 3) continue;
		// sort by (-freq, sym), insertion (deterministic)
		var q: usize = 1;
		while (q < nsym) : (q += 1) {
			const s = syms_buf[q];
			var r = q;
			while (r > 0 and (pass.freqs[syms_buf[r - 1]] < pass.freqs[s] or
					(pass.freqs[syms_buf[r - 1]] == pass.freqs[s] and syms_buf[r - 1] > s))) : (r -= 1) {
				syms_buf[r] = syms_buf[r - 1];
			}
			syms_buf[r] = s;
		}
		const syms = syms_buf[0..@min(nsym, POLISH_TRIPLE_SYMS)];
		for (syms) |x| {
			for (syms) |y| {
				for (syms) |z| {
					if (x != y and x != z and y < z) {
						tris[nt] = .{ .x = x, .y = y, .z = z };
						nt += 1;
						if (nt == POLISH_TRIPLE_CAP) break :outer;
					}
				}
			}
		}
	}
	for (tris[0..nt]) |t| {
		const d0 = seq[t.x];
		if (seq[t.y] != d0 or seq[t.z] != d0 or d0 <= 1 or d0 >= 15) continue;
		const dp = @as(i64, pass.freqs[t.y]) + pass.freqs[t.z] - pass.freqs[t.x];
		const dd = polishSpanDeltaState(&pass.st, &.{ t.x, t.y, t.z }, &.{ d0 - 1, d0 + 1, d0 + 1 }, clc, false) + dp;
		if (dd < 0 and pass.tryApply(&.{ t.x, t.y, t.z }, &.{ d0 - 1, d0 + 1, d0 + 1 }, dp)) {
			dp_total += dp;
			improved = true;
		}
	}
	return .{ .dp = dp_total, .improved = improved };
}

/// Allowed code sets: complete, empty, or one code of length one.
/// lone_len is the surviving length when ncodes == 1. min_codes applies
/// the distance-code floor; lit/len uses zero.
fn polishLegal(kraft: i64, ncodes: usize, lone_len: u8, min_codes: usize) bool {
	if (ncodes < min_codes) return false;
	if (kraft == KRAFT_FULL or ncodes == 0) return true;
	return ncodes == 1 and lone_len == 1;
}

/// Structural-phase positions: grant/relocate destinations below both
/// grant_cap and the last nonzero entry (so trimming never grows the
/// section), dead coded symbols, and live symbols.
const StructViews = struct {
	zeros: [288]usize,
	nz: usize,
	dead: [288]usize,
	ndead: usize,
	live: [288]usize,
	nlive: usize,
};

fn structViews(seq: []const u8, freqs: []const u32, grant_cap: usize, v: *StructViews) void {
	const n = seq.len;
	var last_nz: usize = 0;
	var has_nz = false;
	for (0..n) |i| {
		if (seq[i] > 0) {
			last_nz = i;
			has_nz = true;
		}
	}
	v.nz = 0;
	v.ndead = 0;
	v.nlive = 0;
	const zcap = @min(n, grant_cap);
	for (0..zcap) |i| {
		if (seq[i] == 0 and has_nz and i < last_nz) {
			v.zeros[v.nz] = i;
			v.nz += 1;
		}
	}
	for (0..n) |i| {
		if (seq[i] > 0) {
			if (freqs[i] == 0) {
				v.dead[v.ndead] = i;
				v.ndead += 1;
			} else {
				v.live[v.nlive] = i;
				v.nlive += 1;
			}
		}
	}
}

const StructPass = struct {
	seq: []u8,
	clc: *const [19]i64,
	st: PolishState,
	dp_total: i64,
	improved: bool,

	/// Screen, then confirm by DP; mutate seq only on acceptance.
	fn tryMove(self: *StructPass, positions: []const usize, newvals: []const u8, dp: i64) bool {
		if (polishSpanDeltaState(&self.st, positions, newvals, self.clc, false) + dp >= 0) return false;
		const delta = polishSpanDeltaState(&self.st, positions, newvals, self.clc, true);
		if (delta + dp >= 0) return false;
		for (positions, newvals) |q, w| self.seq[q] = w;
		self.dp_total += dp;
		self.improved = true;
		polishBuild(&self.st, self.seq, self.clc);
		return true;
	}
};

/// Structural tree moves: revoke, relocate, revoke+promote, grant+demote.
/// Each move preserves an allowed code set. Each move class starts from
/// a snapshot of position views; accepted moves recompute those views.
fn polishStructuralPass(seq: []u8, freqs: []const u32, clc: *const [19]i64, grant_cap: usize, min_codes: usize) PolishPassResult {
	if (active_optimizer_memo) |memo| {
		if (seq.len <= 288) {
			const slot = memo.sweepSlot(.structural, seq, freqs, clc, grant_cap, min_codes);
			if (slot.replay(.structural, seq, freqs, clc, grant_cap, min_codes)) |result| {
				memo.sweep_hits += 1;
				return result;
			}
			memo.sweep_misses += 1;
			var input: [288]u8 = undefined;
			@memcpy(input[0..seq.len], seq);
			const result = polishStructuralPassUncached(seq, freqs, clc, grant_cap, min_codes);
			slot.save(.structural, input[0..seq.len], freqs, clc, grant_cap, min_codes, seq, result);
			return result;
		}
	}
	return polishStructuralPassUncached(seq, freqs, clc, grant_cap, min_codes);
}

/// min_codes: the section's codeword floor (min_dist_codes for the distance
/// section, 0 for lit/len). An entry state below it is an inherited hazard
/// (pass-through, phase skipped); a revoke may never cross it.
fn polishStructuralPassUncached(seq: []u8, freqs: []const u32, clc: *const [19]i64, grant_cap: usize, min_codes: usize) PolishPassResult {
	const n = seq.len;
	var kraft: i64 = 0;
	var ncodes: usize = 0;
	var max_len: u8 = 0;
	for (seq) |l| {
		if (l > 0) {
			kraft += @as(i64, 1) << @intCast(15 - l);
			ncodes += 1;
			max_len = @max(max_len, l);
		}
	}
	// Skip structural moves on incomplete input trees or trees below the
	// configured floor. Such inherited encodings remain eligible unchanged.
	if (!polishLegal(kraft, ncodes, max_len, min_codes)) return .{ .dp = 0, .improved = false };
	var buffers: PolishBuffers = undefined;
	var sp: StructPass = .{
		.seq = seq,
		.clc = clc,
		.st = buffers.state(n),
		.dp_total = 0,
		.improved = false,
	};
	polishBuild(&sp.st, seq, clc);
	var v: StructViews = undefined;
	structViews(seq, freqs, grant_cap, &v);
	var snap: [288]usize = undefined;
	var zsnap: [288]usize = undefined;

	// 1) revoke: drop a dead code outright where the remainder stays legal
	//    (in practice: dist-section endgames — dummy-dist cleanup)
	{
		const nd = v.ndead;
		@memcpy(snap[0..nd], v.dead[0..nd]);
		for (snap[0..nd]) |j| {
			const d = seq[j];
			if (d == 0) continue;
			var lone: u8 = 0;
			if (ncodes == 2) {
				for (0..n) |i| {
					if (seq[i] != 0 and i != j) lone = @max(lone, seq[i]);
				}
			}
			if (!polishLegal(kraft - (@as(i64, 1) << @intCast(15 - d)), ncodes - 1, lone, min_codes)) continue;
			if (sp.tryMove(&.{j}, &.{0}, 0)) {
				kraft -= @as(i64, 1) << @intCast(15 - d);
				ncodes -= 1;
				structViews(seq, freqs, grant_cap, &v);
			}
		}
	}

	// 2) relocate: move a dead code to an absent position (Kraft-neutral,
	//    multiset preserved -> legality preserved)
	{
		const nd = v.ndead;
		@memcpy(snap[0..nd], v.dead[0..nd]);
		for (snap[0..nd]) |j| {
			const d = seq[j];
			if (d == 0) continue;
			const nz = v.nz;
			@memcpy(zsnap[0..nz], v.zeros[0..nz]);
			for (zsnap[0..nz]) |i| {
				if (sp.tryMove(&.{ i, j }, &.{ d, 0 }, 0)) {
					structViews(seq, freqs, grant_cap, &v);
					break;
				}
			}
		}
	}

	// 3) revoke+promote: dead code at depth d funds promoting a live symbol
	//    at d to d-1 (Kraft-exact; payload IMPROVES by freq[t]; a >=2-code
	//    legal pre-state is complete, so the post-state stays complete)
	{
		const nd = v.ndead;
		@memcpy(snap[0..nd], v.dead[0..nd]);
		for (snap[0..nd]) |j| {
			const d = seq[j];
			if (d < 2) continue;
			var cands: [288]usize = undefined;
			var nc: usize = 0;
			for (v.live[0..v.nlive]) |t| {
				if (seq[t] == d) {
					cands[nc] = t;
					nc += 1;
				}
			}
			// insertion sort by (-freq, sym)
			var q: usize = 1;
			while (q < nc) : (q += 1) {
				const s = cands[q];
				var r = q;
				while (r > 0 and (freqs[cands[r - 1]] < freqs[s] or
						(freqs[cands[r - 1]] == freqs[s] and cands[r - 1] > s))) : (r -= 1) {
					cands[r] = cands[r - 1];
				}
				cands[r] = s;
			}
			for (cands[0..@min(nc, POLISH_PROMOTE_CANDS)]) |t| {
				if (sp.tryMove(&.{ j, t }, &.{ 0, d - 1 }, -@as(i64, freqs[t]))) {
					ncodes -= 1;
					structViews(seq, freqs, grant_cap, &v);
					break;
				}
			}
		}
	}

	// 4) grant+demote: absent symbol i gets a code at seq[t]+1 while t
	//    demotes to match (Kraft-exact). Complete sections only: from the
	//    legal single-len-1 state this would manufacture an illegal {2,2}.
	//    Arrival pruning: the granted code must
	//    join an existing run of d or sit next to t (which becomes d).
	if (kraft == KRAFT_FULL) {
		var ts: [288]usize = undefined;
		var ntc: usize = 0;
		for (v.live[0..v.nlive]) |t| {
			ts[ntc] = t;
			ntc += 1;
		}
		for (v.dead[0..v.ndead]) |t| {
			ts[ntc] = t;
			ntc += 1;
		}
		// insertion sort by (freq, sym) ascending — total order, so the
		// live/dead concatenation order is irrelevant
		var q: usize = 1;
		while (q < ntc) : (q += 1) {
			const s = ts[q];
			var r = q;
			while (r > 0 and (freqs[ts[r - 1]] > freqs[s] or
					(freqs[ts[r - 1]] == freqs[s] and ts[r - 1] > s))) : (r -= 1) {
				ts[r] = ts[r - 1];
			}
			ts[r] = s;
		}
		for (ts[0..@min(ntc, POLISH_DEMOTE_SYMS)]) |t| {
			if (seq[t] == 0 or seq[t] + 1 > 15) continue;
			const d = seq[t] + 1;
			const nz = v.nz;
			@memcpy(zsnap[0..nz], v.zeros[0..nz]);
			for (zsnap[0..nz]) |i| {
				const adj = (i + 1 == t) or (i == t + 1) or
					(i > 0 and seq[i - 1] == d) or
					(i + 1 < n and seq[i + 1] == d);
				if (!adj) continue;
				if (sp.tryMove(&.{ i, t }, &.{ d, d }, @as(i64, freqs[t]))) {
					ncodes += 1;
					structViews(seq, freqs, grant_cap, &v);
					break;
				}
			}
		}
	}

	if (std.debug.runtime_safety) {
		var k2: i64 = 0;
		var nc2: usize = 0;
		for (seq) |l| {
			if (l > 0) {
				k2 += @as(i64, 1) << @intCast(15 - l);
				nc2 += 1;
			}
		}
		std.debug.assert(k2 == kraft and nc2 == ncodes);
	}
	return .{ .dp = sp.dp_total, .improved = sp.improved };
}

// Bound this local walk independently of the outer portfolio restart loop.
const POLISH_BC_ROUNDS = 8;

/// Apply a payload-optimal same-depth triple to a fresh copy of seq, or
/// return null if too few symbols have that depth. Sort by (-frequency,
/// symbol); the forward move promotes the first and demotes the last two.
fn polishTripleSeq(alloc: std.mem.Allocator, seq: []const u8, freqs: []const u32, d: u8, inverse: bool) !?[]u8 {
	if (d < 2 or d >= 15) return null;
	var syms_buf: [288]usize = undefined;
	if (!inverse) {
		var nsym: usize = 0;
		for (seq, 0..) |v, i| {
			if (v == d) {
				syms_buf[nsym] = i;
				nsym += 1;
			}
		}
		if (nsym < 3) return null;
		sortByFreqDesc(syms_buf[0..nsym], freqs);
		const s = try alloc.dupe(u8, seq);
		s[syms_buf[0]] = d - 1;
		s[syms_buf[nsym - 2]] = d + 1;
		s[syms_buf[nsym - 1]] = d + 1;
		return s;
	}
	var nup: usize = 0;
	var downs_buf: [288]usize = undefined;
	var ndown: usize = 0;
	var x: usize = 0;
	for (seq, 0..) |v, i| {
		if (v == d - 1) {
			// running min by (freq, sym): later i only wins on strictly
			// smaller freq
			if (nup == 0 or freqs[i] < freqs[x]) x = i;
			nup += 1;
		} else if (v == d + 1) {
			downs_buf[ndown] = i;
			ndown += 1;
		}
	}
	if (nup == 0 or ndown < 2) return null;
	sortByFreqDesc(downs_buf[0..ndown], freqs);
	const s = try alloc.dupe(u8, seq);
	s[x] = d;
	s[downs_buf[0]] = d;
	s[downs_buf[1]] = d;
	return s;
}

fn sortByFreqDesc(syms: []usize, freqs: []const u32) void {
	var q: usize = 1;
	while (q < syms.len) : (q += 1) {
		const s = syms[q];
		var r = q;
		while (r > 0 and (freqs[syms[r - 1]] < freqs[s] or
				(freqs[syms[r - 1]] == freqs[s] and syms[r - 1] > s))) : (r -= 1) {
			syms[r] = syms[r - 1];
		}
		syms[r] = s;
	}
}

const ExactFound = struct { is_ll: bool, sv: []u8, dp: i64, total: i64 };

/// Compare same-depth triples by exact cost: literal/length then distance,
/// ascending depth, forward before inverse, x1 before x2. Accept strict gains.
fn polishExactPass(alloc: std.mem.Allocator, cost_scratch: *std.heap.ArenaAllocator, ll: []u8, dist: []u8, llf: []const u32, df: []const u32, cur_dp: i64) !?ExactFound {
	const tl = trim(ll, common.EOB + 1);
	const td = trim(dist, 1);
	var built = try buildClCost(cost_scratch, tl, td);
	const base_total = built.header_bits + cur_dp;
	var best: ?ExactFound = null;
	const sections = [2]struct { is_ll: bool, seq: []u8, freqs: []const u32 }{
		.{ .is_ll = true, .seq = ll, .freqs = llf },
		.{ .is_ll = false, .seq = dist, .freqs = df },
	};
	for (sections) |sec| {
		var any = false;
		for (sec.seq) |v| {
			if (v != 0) any = true;
		}
		if (!any) continue;
		var d: u8 = 2;
		while (d < 15) : (d += 1) {
			for ([2]bool{ false, true }) |inv| {
				const s1 = (try polishTripleSeq(alloc, sec.seq, sec.freqs, d, inv)) orelse continue;
				var cands_buf: [2][]u8 = undefined;
				cands_buf[0] = s1;
				var ncand: usize = 1;
				if (try polishTripleSeq(alloc, s1, sec.freqs, d, inv)) |s2| {
					cands_buf[1] = s2;
					ncand = 2;
				}
				for (cands_buf[0..ncand]) |sv| {
					var dp = cur_dp;
					for (sec.freqs, sv, sec.seq) |f, nv, ov| {
						if (nv != ov) dp += @as(i64, f) * (@as(i64, nv) - ov);
					}
					const ta = trim(sv, if (sec.is_ll) common.EOB + 1 else 1);
					built = if (sec.is_ll)
						try buildClCost(cost_scratch, ta, td)
					else
						try buildClCost(cost_scratch, tl, ta);
					const total = built.header_bits + dp;
					if (total < base_total and (best == null or total < best.?.total)) {
						best = .{ .is_ll = sec.is_ll, .sv = sv, .dp = dp, .total = total };
					}
				}
			}
		}
	}
	return best;
}

const PolishResult = struct { ll: []u8, dist: []u8 };

/// Return the best exact snapshot of tree lengths, or null if no sweep
/// improves the original. The caller compares the materialized block.
fn polishLengths(alloc: std.mem.Allocator, h: Huff) !?PolishResult {
	const ll = h.ll_lengths;
	const dist = h.dist_lengths;
	// Count actual emissions under this block's trees, including the
	// length-258 fallback to symbol 284 plus extra value 31.
	const llf = try alloc.alloc(u32, ll.len);
	@memset(llf, 0);
	const df = try alloc.alloc(u32, dist.len);
	@memset(df, 0);
	const has285 = ll.len > 285 and ll[285] > 0;
	for (h.tokens) |tok| switch (tok) {
		.lit => |b| llf[b] += 1,
		.match => |m| {
			var sym: usize = lenCodeTable[m.length].code;
			if (m.length == common.MAX_MATCH_LENGTH and !has285) sym = 284;
			llf[sym] += 1;
			df[distCodeTable[m.distance].code] += 1;
		},
	};
	llf[common.EOB] += 1;
	if (active_optimizer_memo) |memo| {
		if (ll.len <= 288 and dist.len <= 32) {
			const slot = memo.polishSlot(ll, dist, llf, df);
			if (slot.valid and slot.ll_len == ll.len and slot.dist_len == dist.len and slot.t24 == cl_t24_arbitration and
				slot.floor == min_dist_codes and
				std.mem.eql(u8, slot.lengths[0..ll.len], ll) and
				std.mem.eql(u8, slot.lengths[ll.len..][0..dist.len], dist) and
				std.mem.eql(u32, slot.freqs[0..ll.len], llf) and
				std.mem.eql(u32, slot.freqs[ll.len..][0..dist.len], df))
			{
				memo.polish_hits += 1;
				if (slot.result_ll_len == 0) return null;
				return .{ .ll = try alloc.dupe(u8, slot.result[0..slot.result_ll_len]), .dist = try alloc.dupe(u8, slot.result[slot.result_ll_len..][0..slot.result_dist_len]) };
			}
			memo.polish_misses += 1;
			const result = try polishLengthsFromFreqs(alloc, ll, dist, llf, df);
			slot.valid = true;
			slot.ll_len = @intCast(ll.len);
			slot.dist_len = @intCast(dist.len);
			slot.t24 = cl_t24_arbitration;
			slot.floor = min_dist_codes;
			@memcpy(slot.lengths[0..ll.len], ll);
			@memcpy(slot.lengths[ll.len..][0..dist.len], dist);
			@memcpy(slot.freqs[0..ll.len], llf);
			@memcpy(slot.freqs[ll.len..][0..dist.len], df);
			slot.result_ll_len = 0;
			slot.result_dist_len = 0;
			if (result) |r| {
				slot.result_ll_len = @intCast(r.ll.len);
				slot.result_dist_len = @intCast(r.dist.len);
				@memcpy(slot.result[0..r.ll.len], r.ll);
				@memcpy(slot.result[r.ll.len..][0..r.dist.len], r.dist);
			}
			return result;
		}
	}
	return polishLengthsFromFreqs(alloc, ll, dist, llf, df);
}

// Only the starting lengths, symbol emission counts, CL seed mode and distance
// floor affect this search. Extra-bit payloads and token order contribute
// constants.
fn polishLengthsFromFreqs(alloc: std.mem.Allocator, ll_input: []const u8, dist_input: []const u8, llf: []const u32, df: []const u32) !?PolishResult {
	const ll = try alloc.dupe(u8, ll_input);
	const dist = try alloc.dupe(u8, dist_input);

	// Cost-only CL builds use scratch reset after each call. Materialization
	// belongs to polishedOf or optimizeBlockCfg.
	var cost_scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer cost_scratch.deinit();

	var built = try buildClCost(&cost_scratch, ll, dist);
	var best_total = built.header_bits;
	var clc = try polishClCosts(&built.cl_lengths);
	var best_ll: ?[]u8 = null;
	var best_dist: ?[]u8 = null;
	var cur_dp: i64 = 0;

	// Phase A: keep snapshots from the swap/triple walk before trying
	// structural changes, so later exploration cannot discard these winners.
	for (0..POLISH_MAX_SWEEPS) |_| {
		var improved = false;
		const sections = [2]struct { seq: []u8, freqs: []const u32 }{
			.{ .seq = ll, .freqs = llf },
			.{ .seq = dist, .freqs = df },
		};
		for (sections) |sec| {
			var any = false;
			for (sec.seq) |v| {
				if (v != 0) any = true;
			}
			if (!any) continue;
			const res = try polishSectionPass(alloc, sec.seq, sec.freqs, &clc);
			cur_dp += res.dp;
			improved = improved or res.improved;
		}
		built = try buildClCost(&cost_scratch, ll, dist);
		const ex = built.header_bits;
		clc = try polishClCosts(&built.cl_lengths);
		if (ex + cur_dp < best_total) {
			best_total = ex + cur_dp;
			best_ll = try alloc.dupe(u8, ll);
			best_dist = try alloc.dupe(u8, dist);
		}
		if (!improved) break;
	}

	// Alternate structural sweeps and exact-cost same-depth triples.
	// Snapshot structural results on trimmed length vectors.
	for (0..POLISH_BC_ROUNDS) |bc_round| {
		for (0..POLISH_MAX_SWEEPS) |sweep| {
			var improved = false;
			const sections = [2]struct { seq: []u8, freqs: []const u32, grant_cap: usize, min_codes: usize }{
				.{ .seq = ll, .freqs = llf, .grant_cap = 286, .min_codes = 0 },
				.{ .seq = dist, .freqs = df, .grant_cap = 30, .min_codes = min_dist_codes },
			};
			for (sections) |sec| {
				var any = false;
				for (sec.seq) |v| {
					if (v != 0) any = true;
				}
				if (!any) continue;
				const res = polishStructuralPass(sec.seq, sec.freqs, &clc, sec.grant_cap, sec.min_codes);
				cur_dp += res.dp;
				improved = improved or res.improved;
				if (res.improved or sweep > 0 or bc_round > 0) {
					// The first sweep reuses phase A's swap/triple result if
					// structure and screening prices are unchanged. Later
					// sweeps and outer rounds always recheck.
					const res2 = try polishSectionPass(alloc, sec.seq, sec.freqs, &clc);
					cur_dp += res2.dp;
					improved = improved or res2.improved;
				}
			}
			const tl = trim(ll, common.EOB + 1);
			const td = trim(dist, 1);
			built = try buildClCost(&cost_scratch, tl, td);
			const ex = built.header_bits;
			clc = try polishClCosts(&built.cl_lengths);
			if (ex + cur_dp < best_total) {
				best_total = ex + cur_dp;
				best_ll = try alloc.dupe(u8, tl);
				best_dist = try alloc.dupe(u8, td);
			}
			if (!improved) break;
		}
		const found = (try polishExactPass(alloc, &cost_scratch, ll, dist, llf, df, cur_dp)) orelse break;
		if (found.is_ll) {
			@memcpy(ll, found.sv);
		} else {
			@memcpy(dist, found.sv);
		}
		cur_dp = found.dp;
		if (found.total < best_total) {
			best_total = found.total;
			best_ll = try alloc.dupe(u8, trim(ll, common.EOB + 1));
			best_dist = try alloc.dupe(u8, trim(dist, 1));
		}
	}
	if (best_ll == null) return null;
	return .{ .ll = best_ll.?, .dist = best_dist.? };
}

// ── Joint stream×tree coordinate descent ────

const JOINT_CAP = 8;
const JOINT_INPUT_SEED_MAX_RAW = 32768;

/// Stream half-step: optimal expand/keep
/// per input match under a FIXED tree — separable, one pass, ties keep.
/// Returns null when some match is infeasible both ways (only possible
/// for trees not derived from the input).
fn decideStream(alloc: std.mem.Allocator, orig_tokens: []const Token, matches: []const MatchInfo, ll_len: []const u8, dist_len: []const u8) !?[]Token {
	var out: std.ArrayList(Token) = .empty;
	// Keep-mostly streams fit in orig_tokens.len; expansions grow past it.
	try out.ensureTotalCapacity(alloc, orig_tokens.len);
	var m: usize = 0;
	for (orig_tokens, 0..) |tok, i| {
		if (m < matches.len and matches[m].tok_index == i) {
			const mi = matches[m];
			m += 1;
			var keep: ?i64 = null;
			if (mi.dc < dist_len.len and dist_len[mi.dc] != 0) {
				const de: i64 = dist_len[mi.dc];
				if (mi.lc == 285 and (ll_len.len <= 285 or ll_len[285] == 0)) {
					// Length-258 in a tree without symbol 285: priced as
					// 284+31, exactly as assemble/dynBlockCost re-emit it.
					if (ll_len.len > 284 and ll_len[284] != 0)
						keep = @as(i64, ll_len[284]) + 5 + de + mi.dn;
				} else if (mi.lc < ll_len.len and ll_len[mi.lc] != 0) {
					keep = @as(i64, ll_len[mi.lc]) + mi.xn + de + mi.dn;
				}
			}
			var lit: ?i64 = 0;
			// Use the sparse literal histogram: the same price as summing all
			// expanded bytes, with work proportional to distinct byte values.
			for (mi.hist) |hc| {
				if (hc.byte >= ll_len.len or ll_len[hc.byte] == 0) {
					lit = null;
					break;
				}
				lit = lit.? + @as(i64, hc.count) * ll_len[hc.byte];
			}
			if (keep == null and lit == null) return null;
			if (keep == null or (lit != null and lit.? < keep.?)) {
				for (mi.lits) |b| try out.append(alloc, .{ .lit = b });
			} else {
				try out.append(alloc, tok);
			}
		} else {
			try out.append(alloc, tok);
		}
	}
	return out.items;
}

/// The tree polish of h as a materialized candidate, or null.
fn polishedOf(alloc: std.mem.Allocator, h: Huff) !?Huff {
	const pol = (try polishLengths(alloc, h)) orelse return null;
	const built = try buildCl(alloc, pol.ll, pol.dist);
	return .{
		.is_fixed = false,
		.tokens = h.tokens,
		.ll_lengths = pol.ll,
		.dist_lengths = pol.dist,
		.cl_lengths = built.cl_lengths,
		.cl_entries = built.entries.items,
	};
}

/// h with its CL section re-encoded allowing a repeat to cross the ll↔dist
/// boundary (buildClCrossing), or null if no strict gain. Pure header
/// re-encode — tokens and ll/dist lengths untouched — so it never changes
/// which candidate wins arbitration; accept strict gains only.
fn crossingOf(alloc: std.mem.Allocator, h: Huff) !?Huff {
	if (h.is_fixed) return null;
	const cur = try clHeaderBits(&h.cl_lengths, h.cl_entries) +
		@as(i64, @intCast((deflasm.encodingHclen(h) - hclenOf(&h.cl_lengths)) * 3));
	const built = try buildClCrossing(alloc, h.ll_lengths, h.dist_lengths);
	if (built.header_bits >= cur) return null;
	return .{
		.is_fixed = false,
		.tokens = h.tokens,
		.ll_lengths = h.ll_lengths,
		.dist_lengths = h.dist_lengths,
		.cl_lengths = built.cl_lengths,
		.cl_entries = built.entries.items,
	};
}

const JointResult = struct { h: Huff, cost: i64 };

/// Joint coordinate descent from seed: stream
/// fixpoints end the loop with no candidate building; candidates per
/// iterate are kept-tree / canonical-rebuild / polish-of-kept, first
/// strictly-cheaper wins;
/// iterates are adopted on strict gain only.
fn jointDescent(alloc: std.mem.Allocator, seed: Huff, orig_tokens: []const Token, matches: []const MatchInfo, polish_seed: bool) !JointResult {
	var best = seed;
	var best_cost = try dynBlockCost(seed);
	if (polish_seed) {
		if (try polishedOf(alloc, seed)) |pb| {
			const c = try dynBlockCost(pb);
			if (c < best_cost) {
				best = pb;
				best_cost = c;
			}
		}
	}
	for (0..JOINT_CAP) |_| {
		const S = (try decideStream(alloc, orig_tokens, matches, best.ll_lengths, best.dist_lengths)) orelse break;
		if (tokensEqual(S, best.tokens)) break;
		const built = try buildCl(alloc, best.ll_lengths, best.dist_lengths);
		const kept: Huff = .{
			.is_fixed = false,
			.tokens = S,
			.ll_lengths = best.ll_lengths,
			.dist_lengths = best.dist_lengths,
			.cl_lengths = built.cl_lengths,
			.cl_entries = built.entries.items,
		};
		var it_blk = kept;
		var it_cost = try dynBlockCost(kept);
		const canon = (try encoder().complete(alloc, S, false, .{})).body.huff;
		const cc = try dynBlockCost(canon);
		if (cc < it_cost) {
			it_blk = canon;
			it_cost = cc;
		}
		var pb_opt: ?Huff = null;
		if (try polishedOf(alloc, kept)) |pb| {
			pb_opt = pb;
			const pc2 = try dynBlockCost(pb);
			if (pc2 < it_cost) {
				it_blk = pb;
				it_cost = pc2;
			}
		}
		// Append strict-gain boundary-crossing header variants after the kept,
		// rebuilt, and polished candidates. Expanded streams can produce cheaper
		// CL runs across the literal/distance boundary.
		const cross_cands = [_]?Huff{ kept, canon, pb_opt };
		for (cross_cands) |co| {
			if (co) |c| if (try crossingOf(alloc, c)) |xb| {
				const xc = try dynBlockCost(xb);
				if (xc < it_cost) {
					it_blk = xb;
					it_cost = xc;
				}
			};
		}
		if (it_cost < best_cost) {
			best = it_blk;
			best_cost = it_cost;
		} else break;
	}
	return .{ .h = best, .cost = best_cost };
}

const OptResult = struct { block: Block, raw: []const u8, bits: i64 = 0 };

fn litTokens(alloc: std.mem.Allocator, raw: []const u8) ![]Token {
	const toks = try alloc.alloc(Token, raw.len);
	for (raw, 0..) |b, i| toks[i] = .{ .lit = b };
	return toks;
}

/// As-is block cost at the current output offset, including encoding metadata.
fn blockCost(block: Block) !i64 {
	return switch (block.body) {
		.stored => |data| storedCost(data),
		.huff => |h| if (h.is_fixed) fixedCost(h.tokens, h.encoding != null) else try dynBlockCost(h),
	};
}

/// A bounded search may walk uphill. Only its retained record is accepted,
/// and restarting the whole search from each record closes external reruns.
const REPARSE_MAX_RAW = 1024 * 1024;
const REPARSE_ROUNDS = 8;
const FEEDBACK_EVALUATIONS = 16;

fn blockBytes(a: std.mem.Allocator, block: Block) ![]const u8 {
	var out: std.ArrayList(u8) = .empty;
	var writer = common.BitWriter.init(&out, a);
	try deflasm.assembleBlock(&writer, block);
	if (block.is_last) try deflasm.finishDeflate(&writer, block);
	try writer.alignByte();
	return out.items;
}

fn blockFromBytes(a: std.mem.Allocator, bytes: []const u8) !Block {
	var reader = common.BitReader{ .data = bytes };
	return deflasm.parseBlock(&reader, a);
}

/// Complete encoded reads are pure only under the same decoded block and prior
/// dictionary. Binding compares and owns those bytes, not a digest or a caller's
/// pointer. Evicting entries keeps this binding alive in its separate arena.
const ProjectionMemo = struct {
	inputs: std.heap.ArenaAllocator,
	arena: std.heap.ArenaAllocator,
	bound: bool = false,
	offset: u3 = 0,
	raw: []const u8 = &.{},
	prior: []const u8 = &.{},
	caches: [3]std.StringHashMapUnmanaged([]const u8) = .{ .empty, .empty, .empty },
	cached_bytes: usize = 0,
	limit: usize = 32 * 1024 * 1024,

	fn deinit(self: *ProjectionMemo) void {
		self.arena.deinit();
		self.inputs.deinit();
		self.* = undefined;
	}

	fn clear(self: *ProjectionMemo) void {
		self.caches = .{ .empty, .empty, .empty };
		_ = self.arena.reset(.free_all);
		self.cached_bytes = 0;
	}

	fn bind(self: *ProjectionMemo, raw: []const u8, prior: []const u8) !void {
		if (self.bound and self.offset == block_offset and std.mem.eql(u8, self.raw, raw) and std.mem.eql(u8, self.prior, prior)) return;
		self.bound = false;
		self.clear();
		_ = self.inputs.reset(.free_all);
		self.raw = try self.inputs.allocator().dupe(u8, raw);
		self.prior = try self.inputs.allocator().dupe(u8, prior);
		self.offset = block_offset;
		self.bound = true;
	}

	fn remember(self: *ProjectionMemo, grade: ExploreRead.Grade, key: []const u8, value: []const u8) !void {
		std.debug.assert(self.bound);
		if (key.len + value.len > self.limit) return;
		if (self.cached_bytes + key.len + value.len > self.limit) self.clear();
		const cache = &self.caches[@intFromEnum(grade)];
		if (cache.contains(key)) return;
		const a = self.arena.allocator();
		try cache.put(a, try a.dupe(u8, key), try a.dupe(u8, value));
		self.cached_bytes += key.len + value.len;
	}
};

test "projection memo isolates decoded bytes history grades and eviction ownership" {
	const a = std.testing.allocator;
	var memo: ProjectionMemo = .{ .inputs = std.heap.ArenaAllocator.init(a), .arena = std.heap.ArenaAllocator.init(a), .limit = 24 };
	defer memo.deinit();
	var raw = [_]u8{ 65, 65, 65 };
	var prior = [_]u8{65};
	try memo.bind(&raw, &prior);
	try memo.remember(.full, "in", "full");
	try memo.remember(.single, "in", "single");
	try std.testing.expectEqualStrings("full", memo.caches[0].get("in").?);
	try std.testing.expectEqualStrings("single", memo.caches[1].get("in").?);
	try std.testing.expect(memo.caches[2].get("in") == null);
	// Matching contents keep work; a caller mutating the same storage must
	// invalidate it, proving the binding owns values rather than pointers.
	try memo.bind(&raw, &prior);
	try std.testing.expect(memo.caches[0].contains("in"));
	raw[0] = 66;
	try memo.bind(&raw, &prior);
	try std.testing.expect(!memo.caches[0].contains("in"));
	try memo.remember(.full, "in", "new");
	prior[0] = 66;
	try memo.bind(&raw, &prior);
	try std.testing.expect(!memo.caches[0].contains("in"));
	try memo.remember(.full, "in", "new");
	try memo.remember(.full, "another", "123456789012");
	try memo.remember(.single, "third", "fourth");
	try std.testing.expect(!memo.caches[0].contains("in"));
	try std.testing.expectEqualStrings("fourth", memo.caches[1].get("third").?);
	try memo.bind(&raw, &prior);
	try std.testing.expect(memo.caches[1].contains("third"));
	try std.testing.expectEqualSlices(u8, &raw, memo.raw);
	try std.testing.expectEqualSlices(u8, &prior, memo.prior);
	const previous = block_offset;
	defer block_offset = previous;
	block_offset = 3;
	try memo.bind(&raw, &prior);
	try std.testing.expect(!memo.caches[1].contains("third"));
}

test "caller memo preserves block results across warm calls and changed history" {
	var memo = try OptimizerMemo.init(std.testing.allocator, 16);
	defer memo.deinit();
	const references = [_]Token{ .{ .match = .{ .length = 9, .distance = 1 } }, .{ .lit = 67 } };
	// The same encoding emits different bytes under these dictionaries. Each
	// cold result is an independent oracle for both first-use and warm scopes.
	for ([_][]const u8{ "A", "B", "A" }) |prior| {
		var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
		defer arena.deinit();
		var sub = std.heap.ArenaAllocator.init(std.testing.allocator);
		defer sub.deinit();
		var states = [_]std.heap.ArenaAllocator{
			std.heap.ArenaAllocator.init(std.testing.allocator),
			std.heap.ArenaAllocator.init(std.testing.allocator),
		};
		defer for (&states) |*state| state.deinit();
		const a = arena.allocator();
		const block = try encoder().complete(a, &references, true, .{});
		const old = swapOptimizerMemo(null);
		defer _ = swapOptimizerMemo(old);
		const cold = try optimizeBlock(a, &sub, &states, block, prior);
		const expected = try blockBytes(a, cold.block);
		_ = swapOptimizerMemo(&memo);
		for (0..2) |_| {
			const warm = try optimizeBlock(a, &sub, &states, block, prior);
			try std.testing.expectEqualStrings(expected, try blockBytes(a, warm.block));
			try std.testing.expectEqualSlices(u8, cold.raw, warm.raw);
			try std.testing.expect(active_optimizer_memo == &memo);
		}
	}
}

fn withinConfirmMargin(cheap_bits: i64, record_bits: i64, margin: i64) bool {
	// The CLI accepts every i64 margin. Widen before adding so even an
	// effectively unbounded margin retains its mathematical meaning.
	return @as(i128, cheap_bits) <= @as(i128, record_bits) + margin;
}

test "confirmation margin compares accepted i64 extremes without overflow" {
	try std.testing.expect(withinConfirmMargin(20, 16, std.math.maxInt(i64)));
	try std.testing.expect(!withinConfirmMargin(0, 16, std.math.minInt(i64)));
	try std.testing.expect(withinConfirmMargin(20, 16, 4));
	try std.testing.expect(!withinConfirmMargin(21, 16, 4));
	try std.testing.expect(withinConfirmMargin(12, 16, -4));
	try std.testing.expect(!withinConfirmMargin(13, 16, -4));
}

const ReparseContext = struct {
	sub: *std.heap.ArenaAllocator,
	states: *[2]std.heap.ArenaAllocator,
	graph: ir.Graph,
	projection: *ProjectionMemo,

	fn feedbackGrade() ExploreRead.Grade {
		return explore_read.feedback_grade orelse explore_read.grade;
	}

	/// Whether the feedback controller's read of `encoded` is already cached.
	pub fn cached(self: *ReparseContext, encoded: []const u8) bool {
		return self.projection.caches[@intFromEnum(feedbackGrade())].contains(encoded);
	}

	/// The feedback controller's exploration read: production's full
	/// projection unless a research grade is selected (`ExploreRead`).
	pub fn polishEncoded(self: *ReparseContext, a: std.mem.Allocator, encoded: []const u8) !Block {
		return self.polishEncodedGrade(a, encoded, feedbackGrade());
	}

	/// A single-pass read of `encoded`, for admitting non-fixed-point contexts.
	pub fn polishEncodedCheap(self: *ReparseContext, a: std.mem.Allocator, encoded: []const u8) !Block {
		return self.polishEncodedGrade(a, encoded, .single);
	}

	/// Re-read `encoded` at full grade when its cheap read is close enough to
	/// the record to matter, or when it is the walk's round winner under
	/// `winner_always`. Null when that consumer's grade is already full or the
	/// candidate is not worth confirming. Every adopted record passes here.
	pub fn confirmEncoded(self: *ReparseContext, a: std.mem.Allocator, encoded: []const u8, cheap_bits: i64, record_bits: i64, walk: bool) !?Block {
		const er = explore_read;
		const grade = if (walk) er.grade else feedbackGrade();
		if (grade == .full) return null;
		if (!((walk and er.winner_always) or withinConfirmMargin(cheap_bits, record_bits, er.margin))) return null;
		const rich = try self.polishEncodedGrade(a, encoded, .full);
		explore_stats.confirms += 1;
		if (try blockCost(rich) < cheap_bits) explore_stats.confirm_gains += 1;
		return rich;
	}

	fn polishEncodedGrade(self: *ReparseContext, a: std.mem.Allocator, encoded: []const u8, grade: ExploreRead.Grade) !Block {
		const g = @intFromEnum(grade);
		if (self.projection.caches[g].get(encoded)) |value| {
			explore_stats.hits[g] += 1;
			return blockFromBytes(a, value);
		}
		explore_stats.reads[g] += 1;
		// Assembly/reparse is a projection boundary: the old portfolio must
		// see precisely the encoding a fresh external invocation would see.
		const normalized = try blockFromBytes(a, encoded);
		const polished = switch (grade) {
			.full => try optimizeBlockFast(a, self.sub, self.states, normalized, self.graph.program),
			.single => blk: {
				// One classic configuration pass: no restart closure or expanded seed portfolio.
				std.debug.assert(!cl_t24_arbitration);
				_ = self.sub.reset(SCRATCH_RESET);
				const pc = try precomputeBlock(self.sub.allocator(), normalized, self.graph.program);
				const pass = try optimizeBlockCfg(self.sub.allocator(), normalized, pc);
				self.graph.program.check(pass.block);
				break :blk pass;
			},
			.assemble => {
				// No optimization: the candidate's own exact cost is the read.
				self.graph.program.check(normalized);
				return normalized;
			},
		};
		const output = try blockBytes(a, polished.block);
		const result = try blockFromBytes(a, output);
		if (try blockCost(result) != polished.bits) @panic("reparse serialized cost mismatch");
		try self.projection.remember(grade, encoded, output);
		return result;
	}

	fn search(self: *ReparseContext, a: std.mem.Allocator, seed: Block) !Block {
		var seen_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
		defer seen_arena.deinit();
		var seen: std.StringHashMapUnmanaged(void) = .empty;
		const sa = seen_arena.allocator();
		// Cycle detection already retains every visited encoding. The walk
		// and incumbent can refer to those immutable bytes directly.
		var current = try blockBytes(sa, seed);
		var best = current;
		var best_bits = try blockCost(seed);
		try seen.put(sa, current, {});
		var round_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
		defer round_arena.deinit();
		for (0..REPARSE_ROUNDS) |_| {
			_ = round_arena.reset(SCRATCH_RESET);
			const ra = round_arena.allocator();
			const state = try blockFromBytes(ra, current);
			if (state.body != .huff) break;
			const h = state.body.huff;
			const prices = try reparse.prices(encoder(), ra, h, .{}, 0, @splat(false));
			const parsed = reparse.parse(ra, self.graph, prices) catch |err| switch (err) {
				error.NonFiniteCost => @panic("finite scale-zero reparse costs overflowed"),
				error.OutOfMemory => return error.OutOfMemory,
			};
			const er = explore_read;
			const nvariants: usize = if (h.is_fixed) 1 else 2;
			var chosen: Block = undefined;
			var chosen_bits: i64 = std.math.maxInt(i64);
			var chosen_bytes: []const u8 = &.{};
			var costs: [2][3]i64 = .{ .{ 0, 0, 0 }, .{ 0, 0, 0 } };
			for (0..nvariants) |v| {
				const variant = try encoder().complete(ra, parsed.tokens, seed.is_last, .{
					.trees = if (v == 0) .{ .fresh = .standard } else .{ .merge = .{ .previous = h } },
					.header = if (v == 0) .full else .crossing,
				});
				const vbytes = try blockBytes(ra, variant);
				const polished = try self.polishEncodedGrade(ra, vbytes, er.grade);
				const cost = try blockCost(polished);
				costs[v][@intFromEnum(er.grade)] = cost;
				if (er.grade == .full and er.measure_agreement) {
					for ([_]ExploreRead.Grade{ .single, .assemble }) |g| {
						costs[v][@intFromEnum(g)] = try blockCost(try self.polishEncodedGrade(ra, vbytes, g));
					}
				}
				if (cost < chosen_bits) {
					chosen = polished;
					chosen_bits = cost;
					chosen_bytes = vbytes;
				}
			}
			explore_stats.rounds += 1;
			if (er.grade == .full and er.measure_agreement and nvariants == 2) {
				// Do the cheap grades rank the two variants as the full read does?
				if (costs[0][0] == costs[1][0]) {
					explore_stats.full_ties += 1;
				} else {
					const full_pick: usize = if (costs[1][0] < costs[0][0]) 1 else 0;
					for (1..3) |g| {
						const pick: usize = if (costs[1][g] < costs[0][g]) 1 else 0;
						if (pick == full_pick) explore_stats.agree[g] += 1 else explore_stats.disagree[g] += 1;
					}
				}
			}
			if (try self.confirmEncoded(ra, chosen_bytes, chosen_bits, best_bits, true)) |rich| {
				chosen = rich;
				chosen_bits = try blockCost(rich);
			}
			const bytes = try blockBytes(ra, chosen);
			// Equality, not a digest alone, decides whether the walk repeats.
			const entry = try seen.getOrPut(sa, bytes);
			if (!entry.found_existing) entry.key_ptr.* = try sa.dupe(u8, bytes);
			if (chosen_bits < best_bits) {
				best_bits = chosen_bits;
				best = entry.key_ptr.*;
			}
			if (entry.found_existing) break;
			current = entry.key_ptr.*;
		}
		if (best_bits > try blockCost(seed)) @panic("reparse lost its incumbent");
		return blockFromBytes(a, best);
	}
};

/// Does `result` satisfy the distance-code floor `want` relative to the
/// block it was optimized from? Stored and fixed blocks always do. A dynamic
/// tree whose code equals the input's own is inherited, including when only
/// its tokens or header are re-encoded and whatever HDIST padding either one
/// is sent with: the floor never repairs a pre-existing hazard, it only stops
/// us from creating one. Otherwise the tree is ours and must carry `want`
/// codewords.
fn satisfiesDistFloor(result: Block, input: Block, want: u8) bool {
	const h = switch (result.body) {
		.stored => return true,
		.huff => |h| h,
	};
	if (h.is_fixed) return true;
	if (input.body == .huff and !input.body.huff.is_fixed) {
		const kept = input.body.huff.dist_lengths;
		if (std.mem.eql(u8, trim(kept, 0), trim(h.dist_lengths, 0))) return true;
	}
	var n: usize = 0;
	for (h.dist_lengths) |l| {
		if (l != 0) n += 1;
	}
	return n >= want;
}

/// The unfloored winner's distance tree completed to the floor: the empty
/// form becomes `want` 1-bit codes, a lone code gets its 1-bit filler at the
/// lowest absent index, the CL section is rebuilt, tokens are unchanged. Its
/// cost is the unfloored result plus the repair's few header bits, so the
/// floored search seeded from it can never lose more than that.
fn repairDistFloor(alloc: std.mem.Allocator, result: Block, want: u8) !Block {
	var h = result.body.huff;
	std.debug.assert(!h.is_fixed);
	var full = [_]u8{0} ** 30;
	@memcpy(full[0..h.dist_lengths.len], h.dist_lengths);
	const n = countNonzero(&full);
	if (n == 0) {
		for (full[0..want]) |*l| l.* = 1;
	} else if (n == 1) {
		const previous = swapMinDistCodes(want);
		defer _ = swapMinDistCodes(previous);
		distFloor(&full);
	}
	std.debug.assert(countNonzero(&full) >= want);
	h.dist_lengths = try alloc.dupe(u8, trim(&full, 1));
	const built = try buildCl(alloc, h.ll_lengths, h.dist_lengths);
	h.cl_lengths = built.cl_lengths;
	h.cl_entries = built.entries.items;
	h.encoding = null;
	return .{ .is_last = result.is_last, .body = .{ .huff = h } };
}

/// Try the unfloored search first. If its result is inherited or meets the
/// floor, keep it unchanged. Otherwise run floored searches from both the input
/// and the repaired winner; ties prefer the input seed. Repeat from strict
/// improvements so the result is a fixed point. Strictly decreasing bits bound
/// the restart loop; the repaired seed bounds the floor's cost.
fn optimizeBlockAtOffset(alloc: std.mem.Allocator, sub: *std.heap.ArenaAllocator, states: *[2]std.heap.ArenaAllocator, block: Block, prior: []const u8, offset: u3) !OptResult {
	const previous = block_offset;
	block_offset = offset;
	defer block_offset = previous;
	return optimizeBlock(alloc, sub, states, block, prior);
}

fn optimizeBlock(alloc: std.mem.Allocator, sub: *std.heap.ArenaAllocator, states: *[2]std.heap.ArenaAllocator, block: Block, prior: []const u8) !OptResult {
	const program = try ir.Program.decode(alloc, block, prior);
	const want = min_dist_codes;
	if (want == 0) return optimizeBlockAt(alloc, sub, states, block, program);
	var current = block;
	var current_bits = try blockCost(block);
	while (true) {
		const unfloored = blk: {
			const previous = swapMinDistCodes(0);
			defer _ = swapMinDistCodes(previous);
			break :blk try optimizeBlockAt(alloc, sub, states, current, program);
		};
		if (satisfiesDistFloor(unfloored.block, current, want)) return unfloored;
		var floored = try optimizeBlockAt(alloc, sub, states, current, program);
		const repaired = try repairDistFloor(alloc, unfloored.block, want);
		const from_repair = try optimizeBlockAt(alloc, sub, states, repaired, program);
		if (from_repair.bits < floored.bits) floored = from_repair;
		if (floored.bits > current_bits) @panic("floored search grew its seed");
		if (floored.bits == current_bits) return floored;
		if (!satisfiesDistFloor(floored.block, current, want)) @panic("floored search built a hazard tree");
		current = floored.block;
		current_bits = floored.bits;
	}
}

fn optimizeBlockAt(alloc: std.mem.Allocator, sub: *std.heap.ArenaAllocator, states: *[2]std.heap.ArenaAllocator, block: Block, program: ir.Program) !OptResult {
	// Share exact work from the initial portfolio through reparsing. A caller
	// may supply a wider scope; search state and budgets are never cached.
	var memo: ?OptimizerMemo = if (reparse_enabled and active_optimizer_memo == null)
		OptimizerMemo.init(std.heap.page_allocator, 8192) catch |err| switch (err) {
			error.InvalidCapacity => unreachable,
			error.OutOfMemory => return error.OutOfMemory,
		}
	else null;
	defer if (memo) |*owned| owned.deinit();
	const old_memo = if (memo) |*owned| swapOptimizerMemo(owned) else active_optimizer_memo;
	defer _ = swapOptimizerMemo(old_memo);
	const baseline = try optimizeBlockFast(alloc, sub, states, block, program);
	if (!reparse_enabled or baseline.block.body != .huff or baseline.raw.len < 3 or baseline.raw.len > REPARSE_MAX_RAW) return baseline;
	var search_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer search_arena.deinit();
	var production_feedback: FeedbackSession = .{ .a = search_arena.allocator(),
		.options = .{ .evaluations = FEEDBACK_EVALUATIONS, .order = feedback_policy.order, .cheap_contexts = feedback_policy.cheap_contexts }, .record_trials = false };
	const selected_feedback = feedback_session orelse &production_feedback;
	const projection = &active_optimizer_memo.?.projection;
	try projection.bind(program.raw(), program.prior());
	var ctx: ReparseContext = .{
		.sub = sub, .states = states,
		.graph = try reparse.candidatesForProgram(search_arena.allocator(), program),
		.projection = projection,
	};
	var current = baseline.block;
	var cost = baseline.bits;
	var winners = [_]std.heap.ArenaAllocator{
		std.heap.ArenaAllocator.init(std.heap.page_allocator),
		std.heap.ArenaAllocator.init(std.heap.page_allocator),
	};
	defer for (&winners) |*winner| winner.deinit();
	var next: usize = 0;
	while (true) {
		_ = winners[next].reset(SCRATCH_RESET);
		var candidate = try ctx.search(winners[next].allocator(), current);
		var candidate_cost = try blockCost(candidate);
		if (candidate_cost > cost) @panic("reparse search grew its seed");
		if (candidate_cost == cost) {
			candidate = try feedback.run(winners[next].allocator(), candidate, ctx.graph, encoder(), &ctx, selected_feedback);
			candidate_cost = try blockCost(candidate);
			if (candidate_cost > cost) @panic("feedback search grew its incumbent");
			if (candidate_cost == cost) break;
		}
		current = candidate;
		cost = candidate_cost;
		next = 1 - next;
	}
	return .{ .block = try dupeBlock(alloc, current), .raw = baseline.raw, .bits = cost };
}

/// Restart the full portfolio from each strictly cheaper emitted winner.
/// Alternating state arenas retain only the current and next pass; their
/// capacity is reused across blocks by the fused stream driver.
fn optimizeBlockFast(alloc: std.mem.Allocator, sub: *std.heap.ArenaAllocator, states: *[2]std.heap.ArenaAllocator, block: Block, program: ir.Program) !OptResult {
	var current = block;
	var cost = try blockCost(block);
	var next: usize = 0;
	while (true) {
		_ = states[next].reset(SCRATCH_RESET);
		const candidate = try optimizeBlockPass(states[next].allocator(), sub, current, program);
		std.debug.assert(candidate.bits >= 0 and candidate.bits <= cost);
		if (candidate.bits == cost) {
			return .{
				.block = try dupeBlock(alloc, current),
				.raw = program.raw(),
				.bits = cost,
			};
		}
		current = candidate.block;
		cost = candidate.bits;
		next = 1 - next;
	}
}

/// CL seed union: run the complete pipeline under both CL-arbitration configs;
/// choose the smaller result, retaining classic on ties. Neither config
/// dominates, so convergence must restart their union, not just one config.
fn optimizeBlockPass(alloc: std.mem.Allocator, sub: *std.heap.ArenaAllocator, block: Block, program: ir.Program) !OptResult {
	// Both configurations read the same verified parse analysis. Search churn
	// lives in `sub`, reset between configurations; the analysis and copied
	// winner live in the caller's state arena until the next restart.
	_ = sub.reset(SCRATCH_RESET);
	const pc = try precomputeBlock(alloc, block, program);
	const classic_s = try optimizeBlockCfg(sub.allocator(), block, pc);
	const classic: OptResult = .{
		.block = try dupeBlock(alloc, classic_s.block),
		.raw = program.raw(),
		.bits = classic_s.bits,
	};
	_ = sub.reset(SCRATCH_RESET);
	cl_t24_arbitration = true;
	defer cl_t24_arbitration = false;
	const t24_s = try optimizeBlockCfg(sub.allocator(), block, pc);
	if (t24_s.bits < classic.bits) {
		return .{ .block = try dupeBlock(alloc, t24_s.block), .raw = classic.raw, .bits = t24_s.bits };
	}
	return classic;
}

// This part depends on tokens, decoded history and CL seed mode, not on the
// input Huffman/CL trees. Keep seed-dependent arbitration and polishing below.
const StreamPortfolio = struct {
	dynamic: Block,
	dynamic_cost: i64,
	fixed: FixedResult,
	all_dynamic_cost: i64,
	all_fixed_cost: i64,
};
fn buildStreamPortfolio(alloc: std.mem.Allocator, block: Block, pc: Precomp) !StreamPortfolio {
	const orig_tokens = pc.tokens;
	const raw = pc.raw;
	// Each search runs under both CL cost models (see optDynamic's baseline
	// comment): greedy cascades where the exact model stalls; neither
	// dominates. Candidate order determines equal-cost ties.
	const dyn_tokens = try optDynamic(alloc, orig_tokens, pc.matches, pc.base_ll_freq, false, .greedy);
	const dyn_tokens_dp = try optDynamic(alloc, orig_tokens, pc.matches, pc.base_ll_freq, false, .search);
	const fix = try optFixed(alloc, orig_tokens, pc.matches);

	var raw_freq = [_]u32{0} ** 286;
	for (raw) |b| raw_freq[b] += 1;
	const all_fix_cost = fixAllLitsCost(raw_freq[0..256]);
	var raw_ll_freq: [286]u32 = raw_freq;
	if (raw_ll_freq[common.EOB] == 0) raw_ll_freq[common.EOB] = 1;
	var empty_dist = [_]u32{0} ** 30;
	const all_dyn_cost = try dynCostFromFreqs(alloc, &raw_ll_freq, &empty_dist, 0, .full);

	// Drop-285 search: gate on the INPUT holding a length-258 match to
	// reroute (the identity stream below is a
	// drop candidate even when the keep-pass expanded every 258-match).
	var has_258_orig = false;
	for (orig_tokens) |tok| switch (tok) {
		.match => |m| {
			if (m.length == common.MAX_MATCH_LENGTH) has_258_orig = true;
		},
		.lit => {},
	};
	var drop_tokens: ?[]Token = null;
	var drop_tokens_dp: ?[]Token = null;
	if (has_258_orig) {
		drop_tokens = try optDynamic(alloc, orig_tokens, pc.matches, pc.base_ll_freq, true, .greedy);
		drop_tokens_dp = try optDynamic(alloc, orig_tokens, pc.matches, pc.base_ll_freq, true, .search);
	}

	// Dynamic-encoding candidates: each distinct token stream (keep-search
	// output, drop-search output, untouched original — greedy expansion is
	// monotone and can overshoot — and the bidirectional-greedy stream,
	// LAST: it may only win strictly, never steal a tie) × each routing
	// (keep-285, plus drop-285 with per-match / flat-+1 tree weightings when
	// the stream holds a 258-match). Keep the first candidate on ties.
	const bidir_tokens = try optDynamicBidir(alloc, orig_tokens, pc.matches, pc.base_ll_freq);
	var streams: [6][]const Token = undefined;
	var ns: usize = 0;
	streams[ns] = dyn_tokens;
	ns += 1;
	const maybe = [_]?[]const Token{ dyn_tokens_dp, drop_tokens, drop_tokens_dp, orig_tokens, bidir_tokens };
	for (maybe) |m| {
		const cand = m orelse continue;
		var dup = false;
		for (streams[0..ns]) |s| {
			if (tokensEqual(cand, s)) dup = true;
		}
		if (!dup) {
			streams[ns] = cand;
			ns += 1;
		}
	}
	const all_routings = [_]encoding.Length258{ .standard, .alternate, .alternate_unit };
	var dyn_blk: Block = undefined;
	var dyn_cost: i64 = std.math.maxInt(i64);
	for (streams[0..ns]) |toks| {
		var has258 = false;
		for (toks) |tok| switch (tok) {
			.match => |m| {
				if (m.length == common.MAX_MATCH_LENGTH) has258 = true;
			},
			.lit => {},
		};
		const n_rt: usize = if (has258) all_routings.len else 1;
		for (all_routings[0..n_rt]) |rt| {
			const cand = try encoder().complete(alloc, toks, block.is_last, .{ .trees = .{ .fresh = rt } });
			const cost = try dynBlockCost(cand.body.huff);
			if (cost < dyn_cost) {
				dyn_blk = cand;
				dyn_cost = cost;
			}
		}
	}
	return .{ .dynamic = dyn_blk, .dynamic_cost = dyn_cost, .fixed = fix, .all_dynamic_cost = all_dyn_cost, .all_fixed_cost = all_fix_cost };
}
fn cloneStreamPortfolio(alloc: std.mem.Allocator, p: StreamPortfolio) !StreamPortfolio {
	var result = p;
	result.dynamic = try dupeBlock(alloc, p.dynamic);
	result.fixed.tokens = try alloc.dupe(Token, p.fixed.tokens);
	return result;
}
const PORTFOLIO_MAX_ENTRY_BYTES = 256 * 1024;

fn streamPortfolio(alloc: std.mem.Allocator, block: Block, pc: Precomp) !StreamPortfolio {
	const orig_tokens = pc.tokens;
	const memo = active_optimizer_memo orelse return buildStreamPortfolio(alloc, block, pc);
	if (!memo.portfolio_enabled) return buildStreamPortfolio(alloc, block, pc);
	const key = try alloc.alloc(u64, orig_tokens.len);
	for (orig_tokens, key) |tok, *value| value.* = switch (tok) {
		.lit => |b| b,
		.match => |m| (@as(u64, 1) << 63) | (@as(u64, m.length) << 17) | (@as(u64, m.distance) << 1) | @intFromBool(m.original_alt258),
	};
	const flags: u8 = @intFromBool(block.is_last) | (@as(u8, @intFromBool(cl_t24_arbitration)) << 1) | (min_dist_codes << 2);
	var hash = std.hash.Wyhash.init(flags);
	hash.update(std.mem.sliceAsBytes(key));
	hash.update(pc.raw);
	const slot = &memo.stream_slots[hash.final() % memo.stream_slots.len];
	if (slot.valid and slot.flags == flags and std.mem.eql(u64, slot.key, key) and std.mem.eql(u8, slot.raw, pc.raw)) {
		memo.portfolio_hits += 1;
		return cloneStreamPortfolio(alloc, slot.portfolio);
	}
	memo.portfolio_misses += 1;
	const result = try buildStreamPortfolio(alloc, block, pc);
	// Bound retained payload, not just entry count. Trees/entries add less
	// than 4 KiB; arena capacity overhead is included in storageBytes().
	const bytes = key.len * @sizeOf(u64) + pc.raw.len + (result.dynamic.body.huff.tokens.len + result.fixed.tokens.len) * @sizeOf(Token) + 4096;
	if (bytes <= PORTFOLIO_MAX_ENTRY_BYTES) {
		slot.valid = false;
		_ = slot.arena.reset(.free_all);
		const a = slot.arena.allocator();
		slot.key = try a.dupe(u64, key);
		slot.raw = try a.dupe(u8, pc.raw);
		slot.portfolio = try cloneStreamPortfolio(a, result);
		slot.flags = flags;
		slot.valid = true;
	}
	return result;
}

test "stream portfolio memo isolates mode keys history and caller ownership" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	var memo = try OptimizerMemo.init(std.testing.allocator, 1);
	defer memo.deinit();
	const previous_memo = swapOptimizerMemo(&memo);
	defer _ = swapOptimizerMemo(previous_memo);
	const previous_mode = cl_t24_arbitration;
	defer cl_t24_arbitration = previous_mode;
	var tokens = [_]Token{ .{ .lit = 65 }, .{ .match = .{ .length = common.MAX_MATCH_LENGTH, .distance = 1 } }, .{ .lit = 66 } };
	for ([_]bool{ false, true }) |mode| {
		cl_t24_arbitration = mode;
		for ([_]bool{ false, true }) |last| {
			for ([_]bool{ false, true }) |spelling| {
				tokens[1].match.original_alt258 = spelling;
				const block = try encoder().complete(a, &tokens, last, .{});
				const pc = try precomputeMatchLits(a, &tokens, try ir.Program.decode(a, block, &.{}));
				const expected = try buildStreamPortfolio(a, block, pc);
				const misses = memo.portfolio_misses;
				var first = try streamPortfolio(a, block, pc);
				try std.testing.expectEqual(misses + 1, memo.portfolio_misses);
				try std.testing.expectEqualDeep(expected, first);
				first.dynamic.body.huff.ll_lengths[65] +%= 1;
				const hits = memo.portfolio_hits;
				const second = try streamPortfolio(a, block, pc);
				try std.testing.expectEqual(hits + 1, memo.portfolio_hits);
				try std.testing.expectEqualDeep(expected, second);
			}
		}
	}
	// History matters through the expanded bytes. Same tokens with different
	// expansions must miss; repeated reads and irrelevant history must hit.
	const references = [_]Token{.{ .match = .{ .length = 3, .distance = 1 } }};
	const block = try encoder().complete(a, &references, true, .{});
	const hits = memo.portfolio_hits;
	for ([_][]const u8{ "A", "B", "XA", "YA" }) |prior| {
		const pc = try precomputeMatchLits(a, &references, try ir.Program.decode(a, block, prior));
		const expected = try buildStreamPortfolio(a, block, pc);
		try std.testing.expectEqualDeep(expected, try streamPortfolio(a, block, pc));
		const warm_hits = memo.portfolio_hits;
		try std.testing.expectEqualDeep(expected, try streamPortfolio(a, block, pc));
		try std.testing.expectEqual(warm_hits + 1, memo.portfolio_hits);
	}
	try std.testing.expectEqual(hits + 5, memo.portfolio_hits);
}

fn precomputeBlock(alloc: std.mem.Allocator, block: Block, program: ir.Program) !Precomp {
	const tokens = switch (block.body) {
		.stored => |data| try litTokens(alloc, data),
		.huff => |h| h.tokens,
	};
	return precomputeMatchLits(alloc, tokens, program);
}

fn optimizeBlockCfg(alloc: std.mem.Allocator, block: Block, pc: Precomp) !OptResult {
	const orig_tokens = pc.tokens;
	const raw = pc.raw;

	const portfolio = try streamPortfolio(alloc, block, pc);
	const dyn_blk = portfolio.dynamic;
	const dyn_cost = portfolio.dynamic_cost;
	const fix = portfolio.fixed;
	const all_dyn_cost = portfolio.all_dynamic_cost;
	const all_fix_cost = portfolio.all_fixed_cost;
	const stor_cost = storedCost(raw);
	const orig_cost = try blockCost(block);

	// Keep the input's trees, re-encode the CL section, and
	// re-decide the stream under the kept codes. With the trees fixed the
	// expand/keep decision is exact and independent per match (cf. optFixed);
	// expand only on strict gain, so ties keep the input stream.
	var reenc_blk: ?Block = null;
	var reenc_cost: i64 = std.math.maxInt(i64);
	switch (block.body) {
		.huff => |h| if (!h.is_fixed) {
			// Every match symbol is coded in the input trees, so decideStream
			// always produces a candidate under those trees.
			const out = (try decideStream(alloc, orig_tokens, pc.matches, h.ll_lengths, h.dist_lengths)).?;
			const built = try buildCl(alloc, h.ll_lengths, h.dist_lengths);
			const rb: Block = .{ .is_last = block.is_last, .body = .{ .huff = .{
				.is_fixed = false,
				.tokens = out,
				.ll_lengths = h.ll_lengths,
				.dist_lengths = h.dist_lengths,
				.cl_lengths = built.cl_lengths,
				.cl_entries = built.entries.items,
			} } };
			reenc_blk = rb;
			reenc_cost = try dynBlockCost(rb.body.huff);
		},
		.stored => {},
	}

	const best = @min(@min(@min(dyn_cost, fix.cost), @min(all_dyn_cost, all_fix_cost)), @min(@min(stor_cost, reenc_cost), orig_cost));

	var result: OptResult = blk: {
		if (best == orig_cost) break :blk .{ .block = block, .raw = raw };
		if (best == reenc_cost) break :blk .{ .block = reenc_blk.?, .raw = raw };
		if (best == stor_cost) break :blk .{ .block = .{ .is_last = block.is_last, .body = .{ .stored = raw } }, .raw = raw };
		if (best == all_fix_cost and all_fix_cost <= fix.cost) {
			break :blk .{ .block = fixedHuffBlock(try litTokens(alloc, raw), block.is_last), .raw = raw };
		}
		if (best == fix.cost) {
			break :blk .{ .block = fixedHuffBlock(fix.tokens, block.is_last), .raw = raw };
		}
		if (best == all_dyn_cost and all_dyn_cost <= dyn_cost) {
			const all_dyn_blk = try encoder().complete(alloc, try litTokens(alloc, raw), block.is_last, .{});
			break :blk .{ .block = all_dyn_blk, .raw = raw };
		}
		break :blk .{ .block = dyn_blk, .raw = raw };
	};

	// Payload-tied tree polish: post-winner, strict gain only (never
	// steals a tie), compared against the winner's actual cost.
	var cur_best = best;
	switch (result.block.body) {
		.huff => |h| if (!h.is_fixed) {
			if (try polishedOf(alloc, h)) |pol_huff| {
				const pol_cost = try dynBlockCost(pol_huff);
				if (pol_cost < cur_best) {
					result.block = .{ .is_last = block.is_last, .body = .{ .huff = pol_huff } };
					cur_best = pol_cost;
				}
			}
		},
		.stored => {},
	}

	// Joint stream×tree coordinate descent, post-polish, strict gain
	// only. Two seeds:
	// the winner's basin (usually an immediate stream fixpoint) and the
	// input-tree basin (where the legacy tools' joint fixpoints live).
	switch (result.block.body) {
		.huff => |h| if (!h.is_fixed) {
			const jr = try jointDescent(alloc, h, orig_tokens, pc.matches, false);
			if (jr.cost < cur_best) {
				result.block = .{ .is_last = block.is_last, .body = .{ .huff = jr.h } };
				cur_best = jr.cost;
			}
			switch (block.body) {
				.huff => |ih| if (!ih.is_fixed and ih.ll_lengths.len > 0 and raw.len <= JOINT_INPUT_SEED_MAX_RAW) {
					const ibuilt = try buildCl(alloc, ih.ll_lengths, ih.dist_lengths);
					const seed: Huff = .{
						.is_fixed = false,
						.tokens = ih.tokens,
						.ll_lengths = ih.ll_lengths,
						.dist_lengths = ih.dist_lengths,
						.cl_lengths = ibuilt.cl_lengths,
						.cl_entries = ibuilt.entries.items,
					};
					const jr2 = try jointDescent(alloc, seed, orig_tokens, pc.matches, true);
					if (jr2.cost < cur_best) {
						result.block = .{ .is_last = block.is_last, .body = .{ .huff = jr2.h } };
						cur_best = jr2.cost;
					}
				},
				.stored => {},
			}
		},
		.stored => {},
	}

	// CL boundary-crossing polish of the final block (strict gain, pure header
	// re-encode).
	// Catches blocks whose runs RLE cheaper across the ll↔dist boundary but
	// whose stream is a fixpoint (so the descent broke before a candidate).
	switch (result.block.body) {
		.huff => |h| if (!h.is_fixed) {
			if (try crossingOf(alloc, h)) |cb| {
				const cc = try dynBlockCost(cb);
				if (cc < cur_best) {
					result.block = .{ .is_last = block.is_last, .body = .{ .huff = cb } };
					cur_best = cc;
				}
			}
		},
		.stored => {},
	}
	result.bits = cur_best;
	return result;
}

fn tokensEqual(a: []const Token, b: []const Token) bool {
	if (a.len != b.len) return false;
	for (a, b) |x, y| {
		if (std.meta.activeTag(x) != std.meta.activeTag(y)) return false;
		switch (x) {
			.lit => |v| if (v != y.lit) return false,
			.match => |m| if (m.length != y.match.length or m.distance != y.match.distance) return false,
		}
	}
	return true;
}

fn fixedHuffBlock(tokens: []const Token, is_last: bool) Block {
	return .{ .is_last = is_last, .body = .{ .huff = .{
		.is_fixed = true,
		.tokens = tokens,
		.ll_lengths = &.{},
		.dist_lengths = &.{},
		.cl_lengths = [_]u8{0} ** 19,
		.cl_entries = &.{},
	} } };
}

// ── deflate-stream optimizer ─────────────

/// Deep-copy a Block's slices into `a` (POD payloads — Token/ClEntry/u8 hold no
/// nested pointers), so a winning block survives its per-block scratch arena
/// being reset.
fn dupeBlock(a: std.mem.Allocator, b: Block) !Block {
	return switch (b.body) {
		.stored => |data| .{ .is_last = b.is_last, .body = .{ .stored = try a.dupe(u8, data) },
			.alignment_padding = b.alignment_padding },
		.huff => |h| .{ .is_last = b.is_last, .body = .{ .huff = .{
			.is_fixed = h.is_fixed,
			.tokens = try a.dupe(deflasm.Token, h.tokens),
			.ll_lengths = try a.dupe(u8, h.ll_lengths),
			.dist_lengths = try a.dupe(u8, h.dist_lengths),
			.cl_lengths = h.cl_lengths,
			.cl_entries = try a.dupe(deflasm.ClEntry, h.cl_entries),
			.encoding = h.encoding,
		} } },
	};
}

/// Canonical payload codes depend on symbol lengths, not the CL encoding or
/// trailing absent symbols. Fixed books include reserved codes that dynamic
/// literal/length books cannot declare, so the two types cannot be identical.
fn sameCodebooks(a: Huff, b: Huff) bool {
	if (a.is_fixed or b.is_fixed) return a.is_fixed and b.is_fixed;
	return std.mem.eql(u8, trim(a.ll_lengths, 0), trim(b.ll_lengths, 0)) and
		std.mem.eql(u8, trim(a.dist_lengths, 0), trim(b.dist_lengths, 0));
}

test "codebook identity ignores header spelling but includes both alphabets" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	var tokens = [_]Token{ .{ .lit = 65 }, .{ .lit = 66 } };
	const block = try encoder().complete(a, &tokens, true, .{});
	const original = block.body.huff;
	var padded = (try dupeBlock(a, block)).body.huff;
	padded.ll_lengths = try a.alloc(u8, 286);
	padded.dist_lengths = try a.alloc(u8, 30);
	@memset(padded.ll_lengths, 0);
	@memset(padded.dist_lengths, 0);
	@memcpy(padded.ll_lengths[0..original.ll_lengths.len], original.ll_lengths);
	@memcpy(padded.dist_lengths[0..original.dist_lengths.len], original.dist_lengths);
	const cl = try encoder().header(a, padded.ll_lengths, padded.dist_lengths, .greedy);
	padded.cl_entries = cl.entries.items;
	padded.cl_lengths = cl.cl_lengths;
	padded.encoding = .{ .hclen = 19 };
	try std.testing.expect(sameCodebooks(original, padded));
	// Equal literal/length trees do not suffice: distance codewords matter
	// even when this particular token stream contains no matches.
	@memset(padded.dist_lengths[0..4], 2);
	try std.testing.expect(!sameCodebooks(original, padded));
	@memset(padded.dist_lengths, 0);
	@memcpy(padded.dist_lengths[0..original.dist_lengths.len], original.dist_lengths);
	std.mem.swap(u8, &padded.ll_lengths[65], &padded.ll_lengths[common.EOB]);
	try std.testing.expect(!sameCodebooks(original, padded));
	try std.testing.expect(!sameCodebooks(original, fixedHuffBlock(&tokens, true).body.huff));
}

/// Equal-codebook outputs concatenate without recoding their payloads. Own
/// the cheapest header and the tokens until the run's right edge is known.
const HuffmanRun = struct {
	tokens: std.ArrayList(Token) = .empty,
	header_arena: std.heap.ArenaAllocator = std.heap.ArenaAllocator.init(std.heap.page_allocator),
	header: Block = undefined,
	header_bits: i64 = 0,
	payload_bits: i64 = 0,
	blocks: usize = 0,
	joined: bool = false,
	prior: [common.WINDOW_SIZE]u8 = undefined,
	prior_len: usize = 0,
	is_last: bool = false,
	padding: ?deflasm.BitPadding = null,

	fn deinit(self: *HuffmanRun) void {
		self.tokens.deinit(std.heap.page_allocator);
		self.header_arena.deinit();
	}

	fn append(self: *HuffmanRun, block: Block, prior: []const u8) !void {
		const h = block.body.huff;
		std.debug.assert(self.blocks == 0 or sameCodebooks(self.header.body.huff, h));
		var header = block;
		header.body.huff.tokens = &.{};
		const bits = try blockCost(header);
		self.payload_bits += (try blockCost(block)) - bits;
		if (self.blocks == 0 or bits < self.header_bits) {
			_ = self.header_arena.reset(.free_all);
			self.header = try dupeBlock(self.header_arena.allocator(), header);
			self.header_bits = bits;
		}
		if (self.blocks == 0) {
			@memcpy(self.prior[0..prior.len], prior);
			self.prior_len = prior.len;
		}
		const start = self.tokens.items.len;
		try self.tokens.appendSlice(std.heap.page_allocator, h.tokens);
		// Parsed spelling applies only when the source block retained its
		// encoding. The joined block represents the actual emitted tokens.
		if (h.encoding == null) {
			for (self.tokens.items[start..]) |*tok| {
				if (tok.* == .match) tok.match.original_alt258 = false;
			}
		}
		self.blocks += 1;
		self.is_last = block.is_last;
		self.padding = if (h.encoding) |e| e.final_padding else null;
	}

	fn emit(self: *HuffmanRun, w: *common.BitWriter, cfg: *std.heap.ArenaAllocator, states: *[2]std.heap.ArenaAllocator) !bool {
		if (self.blocks == 0) return false;
		defer {
			self.tokens.clearAndFree(std.heap.page_allocator);
			self.blocks = 0;
			self.payload_bits = 0;
		}
		var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
		defer scratch.deinit();
		var block = self.header;
		block.is_last = self.is_last;
		block.body.huff.tokens = self.tokens.items;
		var spelling: deflasm.HuffEncoding = block.body.huff.encoding orelse .{};
		spelling.final_padding = self.padding;
		block.body.huff.encoding = spelling;
		if (self.blocks > 1) {
			self.joined = true;
			block = (try optimizeBlockAtOffset(scratch.allocator(), cfg, states, block, self.prior[0..self.prior_len], @intCast(w.totalBits() & 7))).block;
		}
		const emitted = try emitBlock(w, block, self.prior[0..self.prior_len]);
		self.joined = self.joined or emitted.split;
		if (self.is_last) try deflasm.finishDeflate(w, block);
		return true;
	}
};

/// Lower a cheaper large raw region into legal stored chunks. Search remains
/// over physical blocks: the caller revisits these new boundaries before
/// returning, so a second invocation cannot discover their first optimization.
fn emitBlock(w: *common.BitWriter, block: Block, prior: []const u8) !struct { split: bool, last_header: usize } {
	var last_header = w.out.items.len * 8 + w.cnt;
	if (block.body == .huff) {
		const size = try block.decodedLength();
		if (size > 65535 and storedRegionCost(size, @intCast(last_header & 7)) < try blockCost(block)) {
			var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
			defer arena.deinit();
			const program = try ir.Program.decode(arena.allocator(), block, prior);
			var pos: usize = 0;
			while (pos < size) {
				const end = @min(size, pos + 65535);
				last_header = w.out.items.len * 8 + w.cnt;
				try deflasm.assembleBlock(w, .{ .is_last = block.is_last and end == size, .body = .{ .stored = program.raw()[pos..end] } });
				pos = end;
			}
			return .{ .split = true, .last_header = last_header };
		}
	}
	try deflasm.assembleBlock(w, block);
	return .{ .split = false, .last_header = last_header };
}

/// Settle boundaries and tree/token polishing before discovering new matches
/// in changed blocks. Repeat when reparsing makes further boundary work useful.
fn optimizeDeflateFusedConsumed(a: std.mem.Allocator, out: *std.ArrayList(u8), in: []const u8, consumed_bytes: *usize) deflasm.ParseError!void {
	const start = out.items.len;
	try fusedPasses(a, out, in, consumed_bytes, null);
	if (!boundary_search_enabled) return;
	// Strict byte descent bounds the rounds; a cap would leave work for a second call.
	while (true) {
		var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
		defer scratch.deinit();
		var candidate: std.ArrayList(u8) = .empty;
		defer candidate.deinit(std.heap.page_allocator);
		if (!try boundaryPolish(&candidate, out.items[start..])) break;
		var polished: std.ArrayList(u8) = .empty;
		defer polished.deinit(std.heap.page_allocator);
		if (reparse_enabled) {
			const fresh = try changedBlocks(scratch.allocator(), out.items[start..], candidate.items);
			var consumed: usize = undefined;
			try fusedPasses(std.heap.page_allocator, &polished, candidate.items, &consumed, fresh);
			std.debug.assert(consumed == candidate.items.len);
		} else std.mem.swap(std.ArrayList(u8), &polished, &candidate);
		if (polished.items.len >= out.items.len - start) break;
		out.shrinkRetainingCapacity(start);
		try out.appendSlice(a, polished.items);
		if (!reparse_enabled) break; // The boundary/polish loop already settled this encoding.
	}
}

/// Keep match discovery outside the boundary/polish loop. The first candidate
/// may save only bits; reparsing still gets a chance to turn that into bytes.
fn boundaryPolish(out: *std.ArrayList(u8), stream: []const u8) deflasm.ParseError!bool {
	const previous = swapReparse(false);
	defer _ = swapReparse(previous);
	var current = stream;
	while (true) {
		var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
		defer scratch.deinit();
		const candidate = (try boundaryRound(scratch.allocator(), current)) orelse break;
		var polished: std.ArrayList(u8) = .empty;
		defer polished.deinit(std.heap.page_allocator);
		var consumed: usize = undefined;
		try fusedPasses(std.heap.page_allocator, &polished, candidate.bytes, &consumed, candidate.fresh);
		std.debug.assert(consumed == candidate.bytes.len);
		const shrank = polished.items.len < current.len;
		if (out.items.len != 0 and !shrank) break;
		std.mem.swap(std.ArrayList(u8), out, &polished);
		current = out.items;
		if (!shrank) break;
	}
	return out.items.len != 0;
}

/// Compare decoded spans as well as encodings: a join or split changes indices.
fn changedBlocks(a: std.mem.Allocator, before: []const u8, after: []const u8) deflasm.ParseError![]const bool {
	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	const sa = scratch.allocator();
	const original = try deflasm.parseDeflate(sa, before);
	const blocks = try deflasm.parseDeflate(sa, after);
	return freshBlocks(a, original, try boundary.startsOf(sa, original), blocks, try boundary.startsOf(sa, blocks));
}

fn freshBlocks(a: std.mem.Allocator, original: []const Block, old_starts: []const u32, blocks: []const Block, starts: []const u32) ![]const bool {
	std.debug.assert(old_starts[original.len] == starts[blocks.len]);
	const fresh = try a.alloc(bool, blocks.len);
	var k: usize = 0;
	for (blocks, 0..) |b, i| {
		while (k < original.len and old_starts[k] < starts[i]) k += 1;
		fresh[i] = !(k < original.len and old_starts[k] == starts[i] and old_starts[k + 1] == starts[i + 1] and sameBlock(original[k], b));
	}
	return fresh;
}

const BOUNDARY_INNER_LIMIT = 16;

const BoundaryCandidate = struct { bytes: []u8, fresh: []const bool };

/// Batch boundary searches and tree refits. Only the encoding and change mask
/// survive; decoded bytes and DP storage are released before token polishing.
fn boundaryRound(a: std.mem.Allocator, stream: []const u8) deflasm.ParseError!?BoundaryCandidate {
	var iteration_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer iteration_arena.deinit();
	const ia = iteration_arena.allocator();
	const original = try deflasm.parseDeflate(ia, stream);
	if (original.len == 0) return null;
	const original_dec = try boundary.decode(ia, original);
	// Candidate matches come from the incumbent for the whole round; later
	// iterations can only shorten or drop them, so their own tokens stay reachable.
	const edges = try boundary.edgesOf(ia, original, original_dec);
	// Unchanged blocks borrow earlier iterations' slices; retain them until assembly.
	var blocks = original;
	var dec = original_dec;
	var iterations: usize = 0;
	// Batch cheap refits before the more expensive token/tree polishing.
	while (iterations < BOUNDARY_INNER_LIMIT) : (iterations += 1) {
		const costs = try ia.alloc(u32, blocks.len);
		const overheads = try ia.alloc(u32, blocks.len);
		var input_bits: u64 = 0;
		for (blocks, 0..) |b, i| {
			costs[i] = @intCast(try blockCost(b));
			input_bits += costs[i];
			overheads[i] = 0;
			if (b.body == .huff) {
				var header = b;
				header.body.huff.tokens = &.{};
				overheads[i] = @intCast(try blockCost(header));
			}
		}
		const found = (try boundary.search(ia, blocks, costs, overheads, dec, edges, .{ .slack = boundary_slack })) orelse break;
		var total: u64 = 0;
		for (found.blocks) |b| total += @intCast(try blockCost(b));
		if (total != input_bits - found.before + found.after) @panic("boundary search price differs from assembly");
		for (found.blocks, found.fresh) |*b, f| {
			if (!f or b.body != .huff) continue;
			var refit = try encoder().complete(ia, b.body.huff.tokens, b.is_last, .{});
			if (min_dist_codes > 0) refit = try repairDistFloor(ia, refit, min_dist_codes);
			const refit_bits = try blockCost(refit);
			if (refit_bits < try blockCost(b.*)) {
				b.* = refit;
			}
		}
		blocks = found.blocks;
		dec = .{ .raw = original_dec.raw, .starts = try boundary.startsOf(ia, blocks) };
	}
	if (iterations == 0) return null;
	if (dec.starts[blocks.len] != original_dec.raw.len) @panic("boundary search changed program length");
	for (blocks, dec.starts[0..blocks.len], dec.starts[1..]) |b, start, end| {
		if (start > end or end > original_dec.raw.len) @panic("boundary search produced an invalid span");
		const program = ir.Program{ .bytes = original_dec.raw[0..end], .history = start };
		program.check(b);
	}
	// Fresh: differs from the original block at its span, so it needs the per-block search.
	const fresh = try freshBlocks(a, original, original_dec.starts, blocks, dec.starts);
	var out: std.ArrayList(u8) = .empty;
	try deflasm.assembleDeflate(a, &out, blocks);
	return .{ .bytes = out.items, .fresh = fresh };
}

fn sameBlock(x: Block, y: Block) bool {
	if (x.body == .stored or y.body == .stored) return x.body == .stored and y.body == .stored and std.mem.eql(u8, x.body.stored, y.body.stored);
	const p = x.body.huff;
	const q = y.body.huff;
	if (!sameCodebooks(p, q) or !tokensEqual(p.tokens, q.tokens)) return false;
	return (blockCost(x) catch return false) == (blockCost(y) catch return false);
}

/// A Huffman block that was a per-block fixed point at one offset stays one at
/// another unless stored becomes cheaper there: the offset enters the search
/// only through the stored comparison.
fn storedWinsAtOffset(block: Block, offset: u3) !bool {
	if (block.body != .huff) return true;
	const size = try block.decodedLength();
	return storedRegionCost(size, offset) < try blockCost(block);
}

/// Streaming loop with one reader and one writer.
/// Each block is parsed and optimized in per-block scratch, folded into the
/// 32 KB window, and either emitted or added to the pending Huffman run. Memory
/// holds the output buffer, pending run tokens and one block's working set.
/// parseBlock has no cross-block token dependence: matches stay symbolic;
/// only the optimizer needs decoded context, via the window.
/// Empty blocks are omitted; trailing empties transfer BFINAL to the last
/// emitted header. An entirely empty stream retains one optimized final block.
/// Reports consumed bytes (the final block's last bit rounded up), so callers
/// can walk concatenated streams without a separate probe parse.
fn fusedPasses(a: std.mem.Allocator, out: *std.ArrayList(u8), in: []const u8, consumed_bytes: *usize, fresh: ?[]const bool) deflasm.ParseError!void {
	const start = out.items.len;
	var joined = try optimizeDeflatePass(a, out, in, consumed_bytes, true, fresh);
	var previous: std.ArrayList(u8) = .empty;
	defer previous.deinit(std.heap.page_allocator);
	// Joining can change later offsets; raw lowering creates new boundaries.
	// Revisit affected blocks at the emitted offsets. Joins remove more than
	// seven bits (alignment cannot absorb the gain); splits strictly improve
	// their region and preserve raw bytes. Equal-cost block choices retain the
	// input. Unchanged Huffman blocks at unchanged offsets need only decoding.
	while (joined) {
		previous.clearRetainingCapacity();
		try previous.appendSlice(std.heap.page_allocator, out.items[start..]);
		out.shrinkRetainingCapacity(start);
		var consumed: usize = undefined;
		joined = try optimizeDeflatePass(a, out, previous.items, &consumed, false, null);
		if (std.mem.eql(u8, previous.items, out.items[start..])) break;
	}
}

/// `fresh` (first pass only) marks blocks that need the per-block search;
/// the others are known fixed points and get it only where stored would win
/// at their new offset.
fn optimizeDeflatePass(a: std.mem.Allocator, out: *std.ArrayList(u8), in: []const u8, consumed_bytes: *usize, first_pass: bool, fresh: ?[]const bool) deflasm.ParseError!bool {
	var r = common.BitReader{ .data = in };
	var w = common.BitWriter.init(out, a);
	// Keep only the last 32768 decoded bytes as context for the next block.
	// The stack buffer is reused per member/entry without accumulating
	// allocations in the file arena. wlen <= WINDOW.
	const WINDOW = common.WINDOW_SIZE;
	var window: [WINDOW]u8 = undefined;
	var wlen: usize = 0;
	// Per-block scratch arena. optimizeBlock's candidate search (union driver
	// x2, joint stream×tree descent, tree-polish and CL seed chains, B&B near-ties)
	// allocates heavily, and only the winning block + its decoded raw survive
	// to be assembled/folded — then even they are freed by the reset.
	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	// Config-pass arena for optimizeBlock's union driver; owned here so
	// its capacity survives across blocks.
	var cfg_scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer cfg_scratch.deinit();
	var states = [_]std.heap.ArenaAllocator{
		std.heap.ArenaAllocator.init(std.heap.page_allocator),
		std.heap.ArenaAllocator.init(std.heap.page_allocator),
	};
	defer for (&states) |*state| state.deinit();
	var last_header: ?usize = null;
	var run: HuffmanRun = .{};
	defer run.deinit();
	var index: usize = 0;
	while (true) : (index += 1) {
		_ = scratch.reset(SCRATCH_RESET);
		const source_offset: u3 = @intCast(r.pos() & 7);
		const b = try deflasm.parseBlock(&r, scratch.allocator());
		const empty = switch (b.body) {
			.stored => |data| data.len == 0,
			.huff => |h| h.tokens.len == 0,
		};
		if (empty) {
			if (!b.is_last) continue;
			if (run.blocks != 0) {
				run.is_last = true;
				run.padding = null;
				_ = try run.emit(&w, &cfg_scratch, &states);
				break;
			}
			if (last_header) |bit| {
				// Every emitted block is at least ten bits, so its header
				// byte has already been flushed from the writer's buffer.
				out.items[bit / 8] |= @as(u8, 1) << @intCast(bit & 7);
				break;
			}
		}
		const pending_bits: usize = if (run.blocks == 0) 0 else @intCast(run.header_bits + run.payload_bits);
		const offset: u3 = @intCast((w.totalBits() + pending_bits) & 7);
		// Huffman outputs are already closed under this search unless their
		// starting offset changed. Stored blocks may be newly lowered chunks.
		const search_it = if (fresh) |f| (index >= f.len or f[index] or b.body == .stored or try storedWinsAtOffset(b, offset)) else (first_pass or b.body == .stored or offset != source_offset);
		var res: OptResult = if (search_it)
			try optimizeBlockAtOffset(scratch.allocator(), &cfg_scratch, &states, b, window[0..wlen], offset)
		else .{ .block = b, .raw = (try ir.Program.decode(scratch.allocator(), b, window[0..wlen])).raw() };
		if (run.blocks != 0 and (res.block.body != .huff or !sameCodebooks(run.header.body.huff, res.block.body.huff))) {
			_ = try run.emit(&w, &cfg_scratch, &states);
			const actual: u3 = @intCast(w.totalBits() & 7);
			if (actual != offset) res = try optimizeBlockAtOffset(scratch.allocator(), &cfg_scratch, &states, b, window[0..wlen], actual);
		}
		if (res.block.body == .huff and (!b.is_last or run.blocks != 0)) {
			try run.append(res.block, window[0..wlen]);
		} else {
			const emitted = try emitBlock(&w, res.block, window[0..wlen]);
			last_header = emitted.last_header;
			run.joined = run.joined or emitted.split;
		}
		// Fold this block's decoded raw into the rolling window (keep the last
		// <=WINDOW bytes) before the next iteration's reset frees res.raw.
		if (res.raw.len >= WINDOW) {
			@memcpy(window[0..WINDOW], res.raw[res.raw.len - WINDOW ..]);
			wlen = WINDOW;
		} else {
			const keep = @min(wlen, WINDOW - res.raw.len);
			if (keep < wlen) std.mem.copyForwards(u8, window[0..keep], window[wlen - keep .. wlen]);
			@memcpy(window[keep .. keep + res.raw.len], res.raw);
			wlen = keep + res.raw.len;
		}
		if (b.is_last) {
			if (!try run.emit(&w, &cfg_scratch, &states)) {
				try deflasm.finishDeflate(&w, res.block);
			}
			break;
		}
	}
	consumed_bytes.* = (r.pos() + 7) / 8;
	try w.alignByte();
	return run.joined;
}

test "stored region costs match assembly at every offset and chunk limit" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const raw = try a.alloc(u8, 131071);
	@memset(raw, 0x5a);
	for (0..8) |offset| {
		for ([_]usize{ 0, 1, 65535, 65536, 131070, 131071 }) |size| {
			var out: std.ArrayList(u8) = .empty;
			var w = common.BitWriter.init(&out, a);
			try w.writeBits(0, @intCast(offset));
			var pos: usize = 0;
			while (true) {
				const end = @min(size, pos + 65535);
				try deflasm.assembleBlock(&w, .{ .is_last = end == size, .body = .{ .stored = raw[pos..end] } });
				if (end == size) break;
				pos = end;
			}
			try std.testing.expectEqual(storedRegionCost(size, @intCast(offset)), @as(i64, @intCast(w.totalBits() - offset)));
		}
	}
}

test "preserved encoding costs and deep copies agree with assembly" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const hex = "05e001040000000010000000000000000000000000000000000000000000000000000000000000000004";
	var extended_hclen: [hex.len / 2]u8 = undefined;
	_ = try std.fmt.hexToBytes(&extended_hclen, hex);
	const cases = [_][]const u8{ "\xf9\x00\x00\xff\xff", "\x03\xfc", &extended_hclen, "\x73\x1c\xf9\x00\x00" };
	for (cases) |data| {
		const blocks = try deflasm.parseDeflate(a, data);
		const b = blocks[0];
		var bits_buf: std.ArrayList(u8) = .empty;
		var w = common.BitWriter.init(&bits_buf, a);
		try deflasm.assembleBlock(&w, b);
		const cost: i64 = switch (b.body) {
			.stored => |raw| storedCost(raw),
			.huff => |h| if (h.is_fixed) fixedCost(h.tokens, h.encoding != null) else try dynBlockCost(h),
		};
		try std.testing.expectEqual(cost, @as(i64, @intCast(w.totalBits())));
		const cloned = try dupeBlock(a, b);
		var out: std.ArrayList(u8) = .empty;
		try deflasm.assembleDeflate(a, &out, &.{cloned});
		try std.testing.expectEqualSlices(u8, data, out.items);
	}
}

test "native encoding metadata survives valid edits and falls back after incompatible edits" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const blocks = try deflasm.parseDeflate(a, "\x73\x1c\xf9\x00\x00");
	var b = blocks[0];
	try std.testing.expect(b.body.huff.tokens[1].match.original_alt258);
	const ordinary = [_]Token{ .{ .lit = 65 }, .{ .match = .{ .length = common.MAX_MATCH_LENGTH, .distance = 1 } } };
	try std.testing.expect(tokensEqual(b.body.huff.tokens, &ordinary));
	var out: std.ArrayList(u8) = .empty;
	// Constructing a new block around parsed tokens reconstructs normally.
	try deflasm.assembleDeflate(a, &out, &.{fixedHuffBlock(b.body.huff.tokens, true)});
	try std.testing.expectEqualSlices(u8, "\x73\x1c\x05\x00", out.items);
	// A changed match length must not re-emit the original length-258 spelling.
	const changed_tokens = try a.dupe(Token, b.body.huff.tokens);
	b.body.huff.tokens = changed_tokens;
	changed_tokens[1].match.length = 3;
	out.clearRetainingCapacity();
	try deflasm.assembleDeflate(a, &out, &.{b});
	const edited = try deflasm.parseDeflate(a, out.items);
	try std.testing.expectEqual(@as(u16, 3), edited[0].body.huff.tokens[1].match.length);
	// A new tree with no 284 invalidates the old preference even when the
	// parsed context is deliberately retained; cost and output must agree.
	changed_tokens[1].match.length = common.MAX_MATCH_LENGTH;
	var rebuilt = try encoder().complete(a, b.body.huff.tokens, true, .{});
	rebuilt.body.huff.encoding = b.body.huff.encoding;
	try std.testing.expectEqual(@as(u8, 0), rebuilt.body.huff.ll_lengths[284]);
	var w = common.BitWriter.init(&out, a);
	out.clearRetainingCapacity();
	try deflasm.assembleBlock(&w, rebuilt);
	try std.testing.expectEqual(try dynBlockCost(rebuilt.body.huff), @as(i64, @intCast(w.totalBits())));
	try w.alignByte();
	const reparsed = try deflasm.parseDeflate(a, out.items);
	try std.testing.expect(!reparsed[0].body.huff.tokens[1].match.original_alt258);
	// An edited CL alphabet can require more entries than the old HCLEN.
	rebuilt.body.huff.encoding = .{ .hclen = 18 };
	rebuilt.body.huff.cl_lengths[15] = 1;
	try std.testing.expectEqual(@as(usize, 19), deflasm.encodingHclen(rebuilt.body.huff));
	// Padding is retained only when its original width fits the new position.
	const stored = (try deflasm.parseDeflate(a, "\xf9\x00\x00\xff\xff"))[0];
	const prefix = fixedHuffBlock(&.{}, false);
	out.clearRetainingCapacity();
	try deflasm.assembleDeflate(a, &out, &.{ prefix, stored });
	const shifted = try a.dupe(u8, out.items);
	var plain = stored;
	plain.alignment_padding = null;
	out.clearRetainingCapacity();
	try deflasm.assembleDeflate(a, &out, &.{ prefix, plain });
	try std.testing.expectEqualSlices(u8, shifted, out.items);
	var last = (try deflasm.parseDeflate(a, "\x03\xfc"))[0];
	var literal = [_]Token{.{ .lit = 144 }};
	last.body.huff.tokens = &literal;
	out.clearRetainingCapacity();
	try deflasm.assembleDeflate(a, &out, &.{last});
	const changed = try a.dupe(u8, out.items);
	last.body.huff.encoding = null;
	out.clearRetainingCapacity();
	try deflasm.assembleDeflate(a, &out, &.{last});
	try std.testing.expectEqualSlices(u8, changed, out.items);
}

/// Options are scoped to this call, including nested research calls.
pub const Options = struct {
	reparse: bool = true,
	boundary_search: bool = false,
	boundary_slack: u32 = (boundary.Options{}).slack,
	min_dist_codes: u8 = 2,
	explore_read: ExploreRead = .{},
	feedback_policy: FeedbackPolicy = .{},
	feedback_session: ?*FeedbackSession = null,
	memo: ?*OptimizerMemo = null,
};

/// Snapshot the legacy research scope for callers migrating from swap* APIs.
pub fn currentOptions() Options {
	return .{ .reparse = reparse_enabled, .boundary_search = boundary_search_enabled, .boundary_slack = boundary_slack, .min_dist_codes = min_dist_codes,
		.explore_read = explore_read, .feedback_policy = feedback_policy,
		.feedback_session = feedback_session, .memo = active_optimizer_memo };
}

fn setOptions(options: Options) void {
	std.debug.assert(options.min_dist_codes <= 2);
	reparse_enabled = options.reparse;
	boundary_search_enabled = options.boundary_search;
	boundary_slack = options.boundary_slack;
	min_dist_codes = options.min_dist_codes;
	explore_read = options.explore_read;
	feedback_policy = options.feedback_policy;
	feedback_session = options.feedback_session;
	active_optimizer_memo = options.memo;
}

pub const Checksum = enum { none, crc32, adler32 };
pub const Result = struct {
	/// End of the first stream, rounded up to a byte. Any suffix is untouched.
	consumed: usize,
	decoded_size: u64,
	/// Zero for .none; otherwise the requested checksum of decoded bytes.
	checksum: u32,
};
pub const StreamError = deflasm.ParseError || error{VerificationFailed};

/// Append one optimized stream and independently verify decoded equality.
/// `in` must not alias `out`. On error, restore the output's original length.
/// Only encoded output lives in `a`; parse/search scratch is recycled per block
/// and verification uses fixed-size windows. No container or file-size policy.
pub fn optimize(a: std.mem.Allocator, out: *std.ArrayList(u8), in: []const u8, options: Options, checksum: Checksum) StreamError!Result {
	const previous = currentOptions();
	setOptions(options);
	defer setOptions(previous);
	const start = out.items.len;
	errdefer out.shrinkRetainingCapacity(start);
	var consumed: usize = undefined;
	try optimizeDeflateFusedConsumed(a, out, in, &consumed);
	std.debug.assert(consumed <= in.len);
	return verify(in[0..consumed], out.items[start..], checksum);
}

/// Inspect one stream without optimizing it. Parse before invoking the
/// independent inflater, which assumes complete input. Used for opaque BGZF.
pub fn inspect(a: std.mem.Allocator, in: []const u8, checksum: Checksum) StreamError!Result {
	var scratch = std.heap.ArenaAllocator.init(a);
	defer scratch.deinit();
	var consumed: usize = undefined;
	_ = try deflasm.parseDeflateConsumed(scratch.allocator(), in, &consumed);
	return verify(in[0..consumed], null, checksum);
}

/// Bit-exact parse/assembly of one stream, reporting its consumed extent.
pub fn roundtrip(a: std.mem.Allocator, out: *std.ArrayList(u8), in: []const u8) deflasm.ParseError!usize {
	const start = out.items.len;
	errdefer out.shrinkRetainingCapacity(start);
	var scratch = std.heap.ArenaAllocator.init(a);
	defer scratch.deinit();
	var consumed: usize = undefined;
	const blocks = try deflasm.parseDeflateConsumed(scratch.allocator(), in, &consumed);
	try deflasm.assembleDeflate(a, out, blocks);
	return consumed;
}

/// Parsed input is required: Zig's independent inflater is not a safe parser
/// for arbitrary truncated streams. Collect integrity during the equality pass.
fn verify(orig: []const u8, opt: ?[]const u8, checksum: Checksum) StreamError!Result {
	const flate = std.compress.flate;
	var in1 = std.Io.Reader.fixed(orig);
	var win1: [flate.max_window_len]u8 = undefined;
	var d1 = flate.Decompress.init(&in1, .raw, &win1);
	var in2 = std.Io.Reader.fixed(opt orelse &.{});
	var win2: [flate.max_window_len]u8 = undefined;
	var d2 = flate.Decompress.init(&in2, .raw, &win2);
	var b1: [65536]u8 = undefined;
	var b2: [65536]u8 = undefined;
	var crc = std.hash.crc.Crc32.init();
	var adler = std.hash.Adler32{};
	var length: u64 = 0;
	while (true) {
		const n1 = d1.reader.readSliceShort(&b1) catch return error.Malformed;
		if (opt != null) {
			const n2 = d2.reader.readSliceShort(&b2) catch return error.VerificationFailed;
			if (n1 != n2 or !std.mem.eql(u8, b1[0..n1], b2[0..n2])) return error.VerificationFailed;
		}
		if (n1 == 0) break;
		switch (checksum) {
			.none => {},
			.crc32 => crc.update(b1[0..n1]),
			.adler32 => adler.update(b1[0..n1]),
		}
		length += n1;
	}
	return .{ .consumed = orig.len, .decoded_size = length,
		.checksum = switch (checksum) { .none => 0, .crc32 => crc.final(), .adler32 => adler.adler } };
}

fn optimizeDeflateBytes(a: std.mem.Allocator, in: []const u8) StreamError![]u8 {
	var out: std.ArrayList(u8) = .empty;
	_ = try optimize(a, &out, in, currentOptions(), .none);
	return out.items;
}

fn inflateEql(orig: []const u8, opt: []const u8) bool {
	_ = verify(orig, opt, .none) catch return false;
	return true;
}

test "stream interface owns extent, integrity, rollback and option scope" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const input = [_]u8{ 1, 3, 0, 0xfc, 0xff, 'a', 'b', 'c', 0xde, 0xad };
	const previous = currentOptions();
	for ([_]bool{ true, false }) |reparse_on| {
		for (0..3) |floor| {
			for ([_]Checksum{ .none, .crc32, .adler32 }) |checksum| {
				var out: std.ArrayList(u8) = .empty;
				try out.appendSlice(a, "prefix");
				const result = try optimize(a, &out, &input, .{
					.reparse = reparse_on, .min_dist_codes = @intCast(floor),
				}, checksum);
				try std.testing.expectEqual(8, result.consumed);
				try std.testing.expectEqual(3, result.decoded_size);
				try std.testing.expectEqual(@as(u32, switch (checksum) {
					.none => 0, .crc32 => std.hash.crc.Crc32.hash("abc"), .adler32 => 0x024d0127,
				}), result.checksum);
				try std.testing.expectEqualSlices(u8, "prefix", out.items[0..6]);
				try std.testing.expectEqualDeep(previous, currentOptions());
			}
		}
	}
	var out: std.ArrayList(u8) = .empty;
	try out.appendSlice(a, "prefix");
	const malformed = [_]u8{ 0, 1, 0, 0xfe, 0xff, 'a', 7 };
	try std.testing.expectError(error.Malformed, optimize(a, &out, &malformed, .{ .reparse = false, .min_dist_codes = 0 }, .none));
	try std.testing.expectEqualSlices(u8, "prefix", out.items);
	try std.testing.expectEqualDeep(previous, currentOptions());
	try std.testing.expectEqual(8, try roundtrip(a, &out, &input));
	try std.testing.expectEqualSlices(u8, input[0..8], out.items[6..]);
	const info = try inspect(a, &input, .crc32);
	try std.testing.expectEqual(8, info.consumed);
	try std.testing.expectEqual(3, info.decoded_size);
	try std.testing.expectEqual(std.hash.crc.Crc32.hash("abc"), info.checksum);
}

test "stream verifier refuses changed output" {
	const good = [_]u8{ 1, 3, 0, 0xfc, 0xff, 'a', 'b', 'c' };
	const changed = [_]u8{ 1, 3, 0, 0xfc, 0xff, 'a', 'b', 'd' };
	try std.testing.expectError(error.VerificationFailed, verify(&good, &changed, .crc32));
}
