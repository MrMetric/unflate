#!/bin/sh
# Build in zig-out/fuzz/:
#   unflate-fuzz         AFL++ instrumented, persistent mode
#   unflate-fuzz-cmplog  the same with CmpLog, for afl-fuzz -c
#   unflate-repro        uninstrumented; one input from stdin or argv[1]
#
# Zig emits LLVM bitcode; afl-clang-lto instruments it at link time together
# with the C driver. The Zig code targets x86-64-v3 (AVX2), so the same
# binaries run here and on Zen 2 or newer.
set -eu
cd "$(dirname "$0")/.."
out=zig-out/fuzz
mkdir -p "$out"

# Per-module flags precede each -M. ReleaseSafe keeps safety checks and
# assertions, so invariant failures abort instead of corrupting silently.
mod="-OReleaseSafe -target x86_64-linux-gnu -mcpu=x86_64_v3 -fno-stack-check -fno-stack-protector -fPIC"
modules="--dep containers $mod -Mroot=fuzz/harness.zig $mod -Mcontainers=src/containers.zig"

zig build-obj -lc -fllvm --name harness -fno-emit-bin -femit-llvm-bc="$out/harness.bc" $modules
afl-clang-lto -O2 -o "$out/unflate-fuzz" fuzz/driver.c "$out/harness.bc" -lzip -lz
AFL_LLVM_CMPLOG=1 afl-clang-lto -O2 -o "$out/unflate-fuzz-cmplog" fuzz/driver.c "$out/harness.bc" -lzip -lz

zig build-obj -lc --name harness -femit-bin="$out/harness.o" $modules
cc -O1 -g -o "$out/unflate-repro" fuzz/driver.c "$out/harness.o" -lzip -lz

echo "built $out/unflate-fuzz, unflate-fuzz-cmplog and unflate-repro"
