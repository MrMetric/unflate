# Evaluation

Build with `zig build`; install GNU gzip, Zopfli, ECT, Wine and Python 3.11 or newer.
Provide the original defluff and DeflOpt.exe executables on `PATH`, or set their
paths in `TOOLS` in `evaluate.py`. Reconstructed implementations are not used.
From this directory:

```sh
python3 evaluate.py --zopfli-version 1.0.3
python3 evaluate.py /path/to/raw-file --results eval/custom.json
```

Without file arguments, the script downloads Canterbury and enwik8. You can
also place `cantrbry.zip` and `enwik8.zip` in `eval/`. Archives are checked against
`eval-corpora.sha256` before extraction. Download sources:
[Canterbury](https://corpus.canterbury.ac.nz/descriptions/) and
[enwik8](https://mattmahoney.net/dc/textdata.html).

The experiment is the short sequence of `run()` calls in `evaluate.py`:
`gzip -9 -n`, then Zopfli with 1, 5, 15 and 30 iterations and ECT levels 1–9,
then default and fast unflate on each baseline (42 runs per input), plus the
original legacy tools. Each baseline gets one run of defluff and one of DeflOpt
(`/bsack`: permit sub-byte gains, silence reports, detect format, preserve metadata).
The search then applies both tools to every distinct output until no new outputs
remain. Equality uses whole-file SHA-256; equal-size and larger outputs are still
explored. The smallest result includes the original baseline as a candidate.
Edit those calls to change settings or chain more operations;
`run()` returns the input ID for a subsequent call. Executable locations are in
`TOOLS`. Zopfli lacks a version switch, so its version is supplied above.

Runs are sequential, one sample each. Wall time includes process startup and
any decoding required for recompression, including Wine startup for DeflOpt.
It excludes downloads, working copies for ECT/DeflOpt, and output verification.
Every output must decode to the original bytes
and have a gzip header without optional metadata or a timestamp. ECT's copy has
filesystem mtime zero because ECT uses that value in its gzip header.

The JSON records environment and tool versions once. Each run records its input,
tool, flags, gzip byte count and seconds. Follow input references and sum seconds
for pipeline time. The `legacy` entry for each baseline refers to its best run
and sums subprocess times across the entire search, including duplicate results;
this is search cost, not just the winning chain's time. The default output is
`eval/results.json`; use a new path for
each experiment. Compressed intermediates are temporary. Completed measurements
are written on normal exit, Ctrl-C or a Python exception; there is no resumption.

`evaluation-results.json` contains 1,828 measurements: the initial 504 across
twelve input files, plus 1,324 calls in 168 exhaustive legacy-tool searches from
the same saved baselines.
ECT levels 5–9 and Zopfli iteration counts 5, 15 and 30 were measured after the
initial sweep, using the same binaries, saved gzip seeds and wall-time scope.
The JSON note records the external thermal governor used for both sweeps.
The measured unflate binary predates this repository's first commit and reports
`unflate unknown (dirty)`. These measurements therefore have no recorded source
revision; they are retained as initial results, not attributed to a later commit.
Run `zig build test` for native contracts, `python3 test_cli.py` for CLI and
container checks against the built binary, and `python3 test_evaluate.py` for
the evaluator's adapters and archive handling. The CLI tests construct their
own fixtures and need no corpus downloads or external compressors.
