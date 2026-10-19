# Fuzzing

AFL++ harness for the optimizer. It looks for crashes (panics, failed
assertions and safety checks, signals) and for outputs whose content differs
from the input.

## Oracle

`driver.c` runs every input through the optimizer and checks the result with
decoders that share no code with it: zlib for DEFLATE, gzip and PNG zlib
streams, libzip for ZIP (CRC-checked). The optimizer's own roundtrip check
uses `std.compress.flate`. For inputs the reference accepts, any accepted
optimizer output must satisfy these checks:

- the output must decode to the same content: the plaintext for deflate and
  gzip; for PNG the chunk sequence with IDAT runs joined and decoded (as
  libpng decodes them: bytes after the zlib stream are ignored) and
  compressed text decoded; for ZIP the entry names, CRCs and contents;
- a container output must not be larger than its input.

By default, optimizer rejections do not fail the harness. With
`UNFLATE_FUZZ_STRICT=1`, rejecting reference-accepted input or changing
reference-rejected input aborts. This also flags deliberate refusals, such
as padded IDAT streams. The deflate target calls `optimizeDeflateBytes`
directly, below the container checks, so its output check is the only one
applied.

Before each run the driver recomputes gzip CRC/ISIZE/FHCRC, PNG chunk CRCs
and zlib FCHECK/Adler-32 (ZIP CRCs are left alone). Without this, nearly
every mutant fails a checksum and never reaches the DEFLATE code or the
content check. `UNFLATE_FUZZ_FIXUP=0` runs inputs unmodified.

Persistent mode runs many inputs in one process, so the optimizer's memo
tables carry entries between unrelated inputs; a stale hit would show up as
a content mismatch. Those memos are also why AFL reports stability below
100%.

## Build and run

Requires AFL++ built with LTO (`afl-clang-lto`), zlib and libzip.

```sh
sh fuzz/build.sh                                   # zig-out/fuzz/
python3 fuzz/make_seeds.py WORK/seeds [FILE ...]   # optional extra seed files
sh fuzz/campaign.sh start WORK 8                   # detached instances
afl-whatsup -s WORK/deflate                        # also gzip, png, zip
sh fuzz/campaign.sh stop WORK
```

`campaign.sh` lists the instances in order of priority; `JOBS` keeps the first
`JOBS` of them. Secondary instances vary `--fast`, the distance-code floor,
CmpLog, strict mode and fixup.

Driver settings (environment):

| Variable | Values |
| --- | --- |
| `UNFLATE_FUZZ_TARGET` | `deflate` (default), `gzip`, `png`, `zip` |
| `UNFLATE_FUZZ_FAST` | `1` = `--fast` |
| `UNFLATE_FUZZ_MIN_DIST_CODES` | `0`, `1`, `2` (default) |
| `UNFLATE_FUZZ_STRICT` | `1` = abort on acceptance disagreement (see above) |
| `UNFLATE_FUZZ_FIXUP` | `0` = no checksum fixup |

## Triage

The repro binary takes the same environment as the instance that found the
input (see the instance name in the campaign plan) and reads one input:

```sh
UNFLATE_FUZZ_TARGET=gzip zig-out/fuzz/unflate-repro WORK/gzip/main/crashes/id:...
```

It prints the outcome or the failed check, with a Zig stack trace for
panics. `UNFLATE_FUZZ_WRITE_FIXED=PATH` writes the input after checksum
fixup, which reproduces with `unflate` itself (raw deflate inputs need a
gzip wrapper).

Instances in `campaign.sh` read seeds from `WORK/seeds/<target>`. Seeds are
capped at 4 KiB to limit optimization time.
