//! Completion-driven controller for the production reparser. Production uses
//! a bounded search over alternative parses that eliminate rare distance codes.
const std = @import("std");
const ir = @import("deflir.zig");
const reparse = @import("deflreparse.zig");
const deferred = @import("deflsearch.zig");
const deflasm = @import("deflasm.zig");
const encoding = @import("deflencoding.zig");
const common = @import("deflcommon.zig");
const A = std.mem.Allocator;
const Block = deflasm.Block;
fn ensure(ok: bool) void { if (!ok) @panic("feedback controller invariant violated"); }

/// Which pending completion gets the next expensive read. `creation` is the
/// round-robin cursor policy (two initial turns to one feedback turn);
/// `assembled` reads the lowest assembled bit count first, a cheap salience
/// estimate of the eventual polished cost.
/// `mixed` alternates the two rules turn by turn: the score exploits the
/// current record, the cursor explores across goals.
pub const Order = enum { creation, assembled, mixed };
pub const Options = struct {
	mode: enum { single, alternatives, feedback } = .feedback,
	order: Order = .creation,
	/// Also admit each completion's single-pass read as a context with its own
	/// tree and goals. Record acceptance follows the configured read/confirmation policy.
	cheap_contexts: bool = false,
	evaluations: usize = 64,
	contexts: usize = 16,
	max_raw: usize = deferred.MAX_QUERY_LENGTH,
	heap_entries: usize = deferred.DEFAULT_HEAP_ENTRIES,
	whole_block: bool = false,
	context_goals: bool = true,
	production_first: bool = true,
	/// Research admission policy; both alphabets use the same query engine.
	symbols: enum { distance, length, both } = .distance,
};
pub const Stats = struct {
	runs: usize = 0, evaluations: usize = 0, duplicate_completions: usize = 0,
	native_cache_hits: usize = 0, polish_calls: usize = 0,
	contexts: usize = 0, context_limit: usize = 0, requests: usize = 0,
	feedback_requests: usize = 0, exhausted: usize = 0, retained: usize = 0,
	worse_contexts: usize = 0, budget_stops: usize = 0, graph_stops: usize = 0,
	queries: usize = 0, shared_queries: usize = 0,
	initialized_positions: usize = 0, packed_answers: usize = 0,
	heap_entries: usize = 0, root_answers: usize = 0, cheap_contexts: usize = 0,
};
pub const Trial = struct {
	run: usize, request: usize, context: usize, anchor: usize,
	mask: ir.SymbolMask, rank: usize, variant: usize, local_price: f64,
	parent_bits: i64, assembled_bits: i64, polished_bits: i64,
	cached: bool, native_cached: bool, output_context: ?usize, improved: bool, production_parse: bool,
};
pub const Session = struct {
	a: A, options: Options = .{}, stats: Stats = .{},
	trials: std.ArrayList(Trial) = .empty,
	record_trials: bool = true,
};

const Encoding = struct { bytes: []const u8, bits: i64 };
fn encode(a: A, block: Block) !Encoding {
	var out: std.ArrayList(u8) = .empty;
	var w = common.BitWriter.init(&out, a);
	try deflasm.assembleBlock(&w, block);
	const bits: i64 = @intCast(w.totalBits());
	if (block.is_last) try deflasm.finishDeflate(&w, block);
	try w.alignByte();
	return .{ .bytes = out.items, .bits = bits };
}
fn decode(a: A, bytes: []const u8) error{OutOfMemory}!Block {
	var r: common.BitReader = .{ .data = bytes };
	return deflasm.parseBlock(&r, a) catch |err| switch (err) {
		error.Malformed => @panic("completed feedback encoding failed to parse"),
		error.OutOfMemory => return error.OutOfMemory,
	};
}

/// Requests are deliberately small transactions in this experiment. The
/// controller and query interfaces do not infer equivalence from rarity.
fn goals(a: A, h: deflasm.Huff, symbols: @FieldType(Options, "symbols")) ![]ir.SymbolMask {
	var lengths: [29]u32 = @splat(0);
	var distances: [30]u32 = @splat(0);
	for (h.tokens) |t| if (t == .match) {
		lengths[common.lenCodeTable[t.match.length].code - common.FIRST_LENGTH_SYMBOL] += 1;
		distances[common.distCodeTable[t.match.distance].code] += 1;
	};
	var masks: std.ArrayList(ir.SymbolMask) = .empty;
	if (symbols != .length) try rareGoals(a, &masks, &distances, 0);
	if (symbols != .distance) try rareGoals(a, &masks, &lengths, ir.LENGTH_MASK_SHIFT);
	return masks.items;
}

fn rareGoals(a: A, masks: *std.ArrayList(ir.SymbolMask), counts: []const u32, shift: u6) !void {
	var previous: ?usize = null;
	for (counts, 0..) |count, sym| {
		if (count == 0) continue;
		if (count > 2) { previous = null; continue; }
		const bit = @as(ir.SymbolMask, 1) << @intCast(sym + shift);
		try masks.append(a, bit);
		if (previous) |p| try masks.append(a, bit | (@as(ir.SymbolMask, 1) << @intCast(p + shift)));
		previous = sym;
	}
	var tail: ir.SymbolMask = 0;
	var uses: u32 = 0;
	var sym: usize = counts.len;
	while (sym > 0) {
		sym -= 1;
		const count = counts[sym];
		if (count == 0) continue;
		if (count > 2 or uses + count > 4) break;
		uses += count;
		tail |= @as(ir.SymbolMask, 1) << @intCast(sym + shift);
	}
	if (@popCount(tail) > 2) try masks.append(a, tail);
}

const Context = struct { block: Block, encoding: Encoding, prices: reparse.Prices };
const Task = struct {
	anchor: usize, context: usize, mask: ir.SymbolMask, request: ?deferred.Request = null,
	answer: ?deferred.Request.Answer = null, rank: usize = 0, variant: usize = 0,
	exhausted: bool = false,
};
const Controller = struct {
	const Key = struct { anchor: usize, context: usize, mask: ir.SymbolMask };
	builder: encoding.Builder,
	a: A, graph: *deferred.Graph, session: *Session,
	contexts: std.ArrayList(Context) = .empty,
	context_ids: std.StringHashMapUnmanaged(usize) = .empty,
	tasks: std.ArrayList(*Task) = .empty,
	task_ids: std.AutoHashMapUnmanaged(Key, void) = .empty,
	initial: usize = 0, initial_cursor: usize = 0, feedback_cursor: usize = 0,

	fn context(c: *Controller, encoded: Encoding) !?usize {
		if (c.context_ids.get(encoded.bytes)) |id| return id;
		if (c.contexts.items.len >= c.session.options.contexts) {
			c.session.stats.context_limit += 1;
			return null;
		}
		const block = try decode(c.a, encoded.bytes);
		if (block.body != .huff or block.body.huff.is_fixed) return null;
		const id = c.contexts.items.len;
		const copy: Encoding = .{ .bytes = try c.a.dupe(u8, encoded.bytes), .bits = encoded.bits };
		try c.contexts.append(c.a, .{ .block = block, .encoding = copy,
			.prices = try reparse.prices(c.builder, c.a, block.body.huff, .{}, 0, @splat(false)) });
		try c.context_ids.put(c.a, copy.bytes, id);
		c.session.stats.contexts += 1;
		return id;
	}
	fn add(c: *Controller, old_anchor: usize, context_id: usize, mask: ir.SymbolMask) !void {
		// No unchanged tokens survive a whole-block request, so its answer
		// depends on the graph and pricing view, not the anchor's old parse.
		const anchor = if (mask == 0) 0 else old_anchor;
		const key: Key = .{ .anchor = anchor, .context = context_id, .mask = mask };
		if (c.task_ids.contains(key)) return;
		try c.task_ids.put(c.a, key, {});
		const task = try c.a.create(Task);
		task.* = .{ .anchor = anchor, .context = context_id, .mask = mask };
		try c.tasks.append(c.a, task);
		c.session.stats.requests += 1;
	}
	fn addGoals(c: *Controller, id: usize) !void {
		for (try goals(c.a, c.contexts.items[id].block.body.huff, c.session.options.symbols)) |mask| try c.add(id, id, mask);
		if (c.session.options.whole_block) try c.add(0, id, 0);
	}
	fn feedback(c: *Controller, task: *const Task, encoded: Encoding) !?usize {
		if (c.session.options.mode != .feedback) return null;
		const before = c.contexts.items.len;
		const id = try c.context(encoded) orelse return null;
		const before_tasks = c.tasks.items.len;
		// Re-price the unresolved original footprint; polishing may have
		// changed its token boundaries or already removed the target symbol.
		try c.add(task.anchor, id, task.mask);
		// A genuinely new completed context can ask for different joint
		// changes too. Its full encoding, not its histogram, identifies it.
		if (c.contexts.items.len > before) {
			if (encoded.bits > c.contexts.items[task.context].encoding.bits) c.session.stats.worse_contexts += 1;
			if (c.session.options.context_goals) try c.addGoals(id)
			else if (c.session.options.whole_block) try c.add(0, id, 0);
		}
		c.session.stats.feedback_requests += c.tasks.items.len - before_tasks;
		return id;
	}
	fn select(c: *Controller, feedback_turn: bool) ?usize {
		const start: usize = if (feedback_turn) c.initial else 0;
		const end: usize = if (feedback_turn) c.tasks.items.len else c.initial;
		if (start == end) return null;
		const cursor = if (feedback_turn) &c.feedback_cursor else &c.initial_cursor;
		for (0..end - start) |_| {
			const id = start + cursor.* % (end - start);
			cursor.* += 1;
			if (!c.tasks.items[id].exhausted) return id;
		}
		return null;
	}
	fn next(c: *Controller, task: *Task) !bool {
		if (task.answer != null) return true;
		const h = c.contexts.items[task.anchor].block.body.huff;
		if (task.mask == 0 and task.rank == 0 and c.session.options.production_first) {
			// Keep the production loop's first answer as a continuation;
			// asking for another answer enters the complete packed stream.
			// No alternative is removed to preserve this scheduling choice.
			const p = c.contexts.items[task.context].prices;
			const parsed = reparse.parse(c.a, c.graph.edges, p) catch |err| switch (err) {
				error.NonFiniteCost => @panic("finite feedback prices overflowed"),
				error.OutOfMemory => return error.OutOfMemory,
			};
			task.answer = .{ .tokens = parsed.tokens, .cost = parsed.predicted - p.ll[common.EOB] };
			return true;
		}
		if (task.request == null) {
			const spans = try deferred.Request.supports(c.a, h.tokens, task.mask);
			ensure(spans.len > 0 and spans.len <= 4);
			task.request = .{ .graph = c.graph, .tokens = h.tokens, .spans = spans,
				.mask = task.mask, .prices = c.contexts.items[task.context].prices };
		}
		task.answer = try task.request.?.next(c.a);
		if (task.answer == null) {
			task.exhausted = true;
			c.session.stats.exhausted += 1;
			return false;
		}
		return true;
	}
};

const Cand = struct { task: usize, bytes: []const u8, bits: i64, rank: usize, variant: usize, seq: usize };

/// A task's pending answer, materialized under its current variant and
/// assembled: the cheap part of an evaluation, without the read. Null when
/// the task is exhausted. The answer stays on the task until `advance`.
fn produce(c: *Controller, sa: A, ca: A, id: usize, seq: *usize, is_last: bool) !?Cand {
	const task = c.tasks.items[id];
	if (task.exhausted) return null;
	if (!(try c.next(task))) return null;
	const answer = task.answer.?;
	const ctx = c.contexts.items[task.context];
	const merge = task.variant == @as(usize, if (task.mask == 0) 1 else 0);
	const candidate = try c.builder.complete(sa, answer.tokens, is_last, .{
		.trees = if (merge) .{ .merge = .{ .previous = ctx.block.body.huff,
			.order = if (task.mask == 0) .occurrence else .symbol } } else .{ .fresh = .standard },
		.header = if (merge) .crossing else .full,
	});
	const request = try encode(sa, candidate);
	seq.* += 1;
	return .{ .task = id, .bytes = try ca.dupe(u8, request.bytes), .bits = request.bits, .rank = task.rank, .variant = task.variant, .seq = seq.* };
}

fn advance(task: *Task, o: Options) void {
	task.variant += 1;
	if (task.variant == 2) {
		task.variant = 0;
		task.rank += 1;
		task.answer = null;
		if (o.mode == .single) task.exhausted = true;
	}
}

/// `backend.polishEncoded` is the production projection/check/cache service. Only
/// completed encodings cross that boundary. The caller owns the incumbent
/// restart policy and supplies the exploration budget.
pub fn run(a: A, seed: Block, edges: reparse.Edges, builder: encoding.Builder, backend: anytype, session: *Session) !Block {
	const raw = edges.program.raw();
	const o = session.options;
	if (o.evaluations == 0) return seed;
	ensure(o.contexts >= 1);
	if (raw.len > o.max_raw or seed.body != .huff or seed.body.huff.is_fixed) return seed;
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer arena.deinit();
	const ca = arena.allocator();
	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	var chart_stats: deferred.Stats = .{ .max_heap_entries = o.heap_entries };
	var graph: deferred.Graph = .{ .a = ca, .edges = edges, .stats = &chart_stats };
	defer {
		inline for (.{ "queries", "shared_queries", "initialized_positions", "packed_answers", "heap_entries", "root_answers" }) |field| {
			@field(session.stats, field) += @field(chart_stats, field);
		}
	}
	var c: Controller = .{ .builder = builder, .a = ca, .graph = &graph, .session = session };
	var best = try encode(ca, seed);
	const seed_id = (try c.context(best)).?;
	try c.addGoals(seed_id);
	c.initial = c.tasks.items.len;
	if (c.initial == 0) return seed;
	const run_id = session.stats.runs;
	session.stats.runs += 1;
	var completed: std.StringHashMapUnmanaged(Encoding) = .empty;
	var evaluations: usize = 0;
	var turns: usize = 0;
	// Pending candidates under assembled-cost ordering: at most one per task,
	// materialized and assembled but not read. The cheap assembled bit count
	// is the salience score; the expensive read goes to the lowest.
	var cands: std.ArrayList(Cand) = .empty;
	var seq: usize = 0;
	var work_limit = false;
	const scored = o.order != .creation;
	if (scored) {
		for (0..c.tasks.items.len) |id| {
			_ = scratch.reset(.retain_capacity);
			const maybe = produce(&c, scratch.allocator(), ca, id, &seq, seed.is_last) catch |err| switch (err) {
				error.WorkLimit => { session.stats.graph_stops += 1; work_limit = true; break; },
				else => |e| return e,
			};
			if (maybe) |x| try cands.append(ca, x);
		}
	}
	while (!work_limit and evaluations < o.evaluations and turns < 8 * o.evaluations) : (turns += 1) {
		_ = scratch.reset(.retain_capacity);
		const sa = scratch.allocator();
		var cd: Cand = undefined;
		if (scored) {
			if (cands.items.len == 0) break;
			var mi: usize = 0;
			var picked = false;
			if (o.order == .mixed and turns % 2 == 1) {
				// Cursor turn: the task the creation policy would choose, if it
				// has a pending candidate; otherwise fall through to the score.
				const feedback_turn = o.mode == .feedback and turns % 3 == 2;
				if (c.select(feedback_turn) orelse c.select(!feedback_turn)) |id| {
					for (cands.items, 0..) |x, i| if (x.task == id) {
						mi = i;
						picked = true;
						break;
					};
				}
			}
			if (!picked) {
				for (cands.items, 0..) |x, i| {
					const m = cands.items[mi];
					if (x.bits < m.bits or (x.bits == m.bits and x.seq < m.seq)) mi = i;
				}
			}
			cd = cands.swapRemove(mi);
		} else {
			// Initial requests keep two turns out of three; feedback has its own
			// cursor, so admitting a new context does not erase old continuations.
			const feedback_turn = o.mode == .feedback and turns % 3 == 2;
			const id = c.select(feedback_turn) orelse c.select(!feedback_turn) orelse break;
			const maybe = produce(&c, sa, ca, id, &seq, seed.is_last) catch |err| switch (err) {
				error.WorkLimit => { session.stats.graph_stops += 1; break; },
				else => |e| return e,
			};
			cd = maybe orelse continue;
		}
		const task = c.tasks.items[cd.task];
		const answer = task.answer.?;
		const ctx = c.contexts.items[task.context];
		var output: Encoding = undefined;
		const cached = completed.get(cd.bytes);
		var native_cached = false;
		if (cached) |hit| {
			output = hit;
			session.stats.duplicate_completions += 1;
		} else {
			native_cached = backend.cached(cd.bytes);
			const polished = try backend.polishEncoded(sa, cd.bytes);
			var result = try encode(sa, polished);
			// A cheaper exploration read can confirm near-record completions
			// at full grade before accepting them.
			const Backend = @typeInfo(@TypeOf(backend)).pointer.child;
			if (@hasDecl(Backend, "confirmEncoded")) {
				if (try backend.confirmEncoded(sa, cd.bytes, result.bits, best.bits, false)) |rich| result = try encode(sa, rich);
			}
			output = .{ .bytes = try ca.dupe(u8, result.bytes), .bits = result.bits };
			try completed.put(ca, cd.bytes, output);
			// Bound logical new requests, independent of backend cache
			// warmth/eviction. Otherwise the cache would change the search,
			// rather than merely its runtime.
			evaluations += 1;
			session.stats.evaluations += 1;
			if (native_cached) session.stats.native_cache_hits += 1
			else session.stats.polish_calls += 1;
		}
		const improved = output.bits < best.bits;
		if (improved) { best = output; session.stats.retained += 1; }
		const tasks_before = c.tasks.items.len;
		const output_context = try c.feedback(task, output);
		if (o.cheap_contexts and cached == null) {
			const Backend = @typeInfo(@TypeOf(backend)).pointer.child;
			if (@hasDecl(Backend, "polishEncodedCheap")) {
				const cheap = try encode(sa, try backend.polishEncodedCheap(sa, cd.bytes));
				if (!std.mem.eql(u8, cheap.bytes, output.bytes)) {
					_ = try c.feedback(task, .{ .bytes = try ca.dupe(u8, cheap.bytes), .bits = cheap.bits });
					session.stats.cheap_contexts += 1;
				}
			}
		}
		if (session.record_trials) try session.trials.append(session.a, .{ .run = run_id, .request = cd.task,
			.context = task.context, .anchor = task.anchor, .mask = task.mask,
			.rank = cd.rank, .variant = cd.variant, .local_price = answer.cost,
			.parent_bits = ctx.encoding.bits, .assembled_bits = cd.bits,
			.polished_bits = output.bits, .cached = cached != null, .native_cached = native_cached,
			.output_context = output_context, .improved = improved,
			.production_parse = task.mask == 0 and cd.rank == 0 and o.production_first });
		advance(task, o);
		if (scored) {
			// The consumed task's next candidate, then first candidates for the
			// tasks this feedback created. Nothing in scratch is live here.
			_ = scratch.reset(.retain_capacity);
			var id = cd.task;
			var k = tasks_before;
			while (true) {
				const maybe = produce(&c, scratch.allocator(), ca, id, &seq, seed.is_last) catch |err| switch (err) {
					error.WorkLimit => { session.stats.graph_stops += 1; work_limit = true; break; },
					else => |e| return e,
				};
				if (maybe) |x| try cands.append(ca, x);
				if (k >= c.tasks.items.len) break;
				id = k;
				k += 1;
			}
		}
	}
	if (evaluations == o.evaluations or turns == 8 * o.evaluations) session.stats.budget_stops += 1;
	return decode(a, best.bytes);
}
