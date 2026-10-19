#!/bin/sh
# Launch a detached AFL++ campaign: one output directory per target, each
# with a main instance and secondaries that vary the optimizer settings.
#
#   sh fuzz/campaign.sh start WORKDIR [JOBS]   seeds from WORKDIR/seeds/<target>
#   sh fuzz/campaign.sh stop WORKDIR
#   afl-whatsup -s WORKDIR/<target>            progress
#
# JOBS (default 8) is the instance count; the plan below is trimmed to it in
# order, so small counts keep the deflate main instance and one per target.
# Restarting resumes from existing output (AFL_AUTORESUME).
set -eu
cd "$(dirname "$0")/.."
cmd=${1:?usage: campaign.sh start|stop WORKDIR [JOBS]}
work=$(realpath "${2:?usage: campaign.sh start|stop WORKDIR [JOBS]}")
jobs=${3:-8}
bin=$PWD/zig-out/fuzz

if [ "$cmd" = stop ]; then
	[ -f "$work/pids" ] || { echo "no $work/pids"; exit 1; }
	# SIGINT lets afl-fuzz write its final state.
	xargs kill -INT < "$work/pids" 2>/dev/null || true
	rm "$work/pids"
	exit 0
fi
[ "$cmd" = start ] || { echo "unknown command $cmd"; exit 2; }
[ -x "$bin/unflate-fuzz" ] || { echo "run fuzz/build.sh first"; exit 1; }
mkdir -p "$work/logs"

# target  role  name     cmplog  environment
plan="deflate -M main 0 -
gzip -M main 0 -
png -M main 1 -
zip -M main 1 -
deflate -S fast 0 UNFLATE_FUZZ_FAST=1
deflate -S cmplog 1 -
deflate -S floor0 0 UNFLATE_FUZZ_MIN_DIST_CODES=0
gzip -S cmplog 1 -
deflate -S strict 0 UNFLATE_FUZZ_STRICT=1
png -S nofixup 0 UNFLATE_FUZZ_FIXUP=0
gzip -S fast 0 UNFLATE_FUZZ_FAST=1
zip -S fast 0 UNFLATE_FUZZ_FAST=1
deflate -S fastcmp 1 UNFLATE_FUZZ_FAST=1
png -S fast 0 UNFLATE_FUZZ_FAST=1
gzip -S strict 0 UNFLATE_FUZZ_STRICT=1
deflate -S floor1 0 UNFLATE_FUZZ_MIN_DIST_CODES=1"

echo "$plan" | head -n "$jobs" | while read -r target role name cmplog extra; do
	[ -d "$work/seeds/$target" ] || { echo "missing $work/seeds/$target"; exit 1; }
	set -- -i "$work/seeds/$target" -o "$work/$target" "$role" "$name" -t 5000
	[ "$cmplog" = 1 ] && set -- "$@" -c "$bin/unflate-fuzz-cmplog"
	[ "$extra" = - ] && extra=
	# The thermostat recognizes the target binaries by name.
	env AFL_NO_UI=1 AFL_AUTORESUME=1 AFL_SKIP_CPUFREQ=1 \
		AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 UNFLATE_FUZZ_TARGET="$target" $extra \
		setsid nohup afl-fuzz "$@" -- "$bin/unflate-fuzz" \
		> "$work/logs/$target-$name.log" 2>&1 < /dev/null &
	echo $! >> "$work/pids"
	echo "started $target/$name ${extra:-}"
done
