# unflate

unflate reduces the size of existing PNG, gzip and ZIP files. It optimizes
DEFLATE codebooks and searches for alternative LZ77 parses while preserving
decoded content and container metadata. It can improve streams produced by
other compressors, and never increases the input file's byte size.

GPT-6 Astra wrote that paragraph. It's accurate, though. And, yes, the code was
written by AIs. I did attempt to make it not a total disaster, though, and you
won't get these results from a lazy oneshot prompt. Code is cheap. Show me the tests. :^)

Headline results:
 * almost always smaller output than running defluff and DeflOpt.exe repeatedly
 * way slower than either of them
 * has fewer bugs than they do (methinks that'd make a fun blog post)
 * works great even after using things like [oxipng](https://github.com/oxipng/oxipng), zopfli, [ECT](https://github.com/fhanau/Efficient-Compression-Tool), [Turtledeflate](https://github.com/rwillenbacher/turtledeflate)
 * doesn't strip metadata, keeps file mtimes, even keeps the same inode :)

Building it needs Zig 0.16.0 (not 0.17.0). I use Arch btw, and that's what's in the repos.
```sh
zig build
./zig-out/bin/unflate image.png archive.gz library.jar
./zig-out/bin/unflate --fast image.png
./zig-out/bin/unflate < input.gz > output.gz
```

I have made no attempt to build or run this anywhere but my Arch Linux PC.

Alright, that's the end of the human touch for now. The rest of this was written by GPT-6 Astra.

## Initial measurements

One sequential sample per stage on an AMD Ryzen 9 5950X running Linux.
The sweep uses gzip `-9 -n`, Zopfli with 1, 5, 15 and 30 iterations, and ECT levels 1–9.
All recompressors start from the gzip seed; baseline pipeline times include
creating that seed. Each unflate mode starts from the baseline independently;
its time is additional. Canterbury totals sum its eleven separately compressed
files. Sizes include the fixed 18-byte gzip envelope, with no filename or timestamp.

The [evaluator](evaluate.py) generates the [complete results](evaluation-results.json),
including tool versions, CPU model, and each run's input, flags, size and time.
[Reproduction instructions](EVALUATION.md) cover downloads, custom inputs,
and compressor chains. Python is needed only for this evaluation tooling.

**Bold** marks the smallest size in each row; *italics* mark sizes larger than
that row's compressor baseline.

### enwik8

| Baseline | Gzip bytes | Pipeline s | +unflate bytes | Added s | +fast bytes | Added s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| gzip -9 | 36,445,241 | 5.16 | **35,071,629** | 238.19 | 36,438,451 | 27.99 |
| Zopfli --i1 | 35,102,371 | 71.39 | **34,991,450** | 227.65 | 35,091,715 | 32.56 |
| Zopfli --i5 | 34,983,757 | 105.26 | **34,947,896** | 196.32 | 34,978,079 | 31.97 |
| Zopfli --i15 | 34,966,078 | 189.57 | **34,937,279** | 194.53 | 34,961,959 | 30.69 |
| Zopfli --i30 | 34,961,453 | 314.70 | **34,934,547** | 193.41 | 34,957,424 | 30.91 |
| ECT -1 | 36,445,241 | 8.44 | **35,071,629** | 233.98 | 36,438,451 | 27.81 |
| ECT -2 | 35,019,433 | 17.44 | **34,966,755** | 172.84 | 35,016,756 | 25.36 |
| ECT -3 | 35,014,536 | 18.48 | **34,956,939** | 189.40 | 35,011,759 | 27.37 |
| ECT -4 | 34,963,574 | 20.86 | **34,952,835** | 80.50 | 34,962,182 | 27.01 |
| ECT -5 | 34,942,789 | 25.04 | **34,938,802** | 82.19 | 34,942,030 | 26.79 |
| ECT -6 | 34,943,936 | 38.09 | **34,940,876** | 91.98 | 34,943,044 | 26.28 |
| ECT -7 | 34,942,341 | 49.68 | **34,939,823** | 91.43 | 34,941,480 | 26.36 |
| ECT -8 | 34,941,118 | 111.49 | **34,938,773** | 88.87 | 34,940,309 | 26.37 |
| ECT -9 | 34,937,774 | 157.90 | **34,935,457** | 90.46 | 34,936,957 | 26.70 |

### Turtledeflate on enwik8 (separate experiment)

Turtledeflate `--9`, followed by one default unflate run, produces:

| Baseline | Gzip bytes | +unflate bytes | Saved bytes | Added s |
| --- | ---: | ---: | ---: | ---: |
| Turtledeflate --9 | 34,932,504 | **34,927,429** | 5,075 | 175.11 |

The Turtledeflate input came from an earlier run using a 16-worker wrapper with
1,000,000-byte superblocks, taking about 22m51s wall time. Unflate was measured
separately on that saved output. Both files decode to the original enwik8 and
use the same fixed 18-byte gzip envelope. This experiment is outside
`evaluate.py` and `evaluation-results.json`; the evaluator does not reproduce it.

### Synthesized enwik8 (research result)

Selecting the smallest compatible blocks across 158 saved enwik8 encodings
produces a 34,920,271-byte gzip. These include Turtledeflate, Zopfli, ECT and
their post-optimized outputs. Adding two records from the hand-optimization and
exact-search lab saves another four bits, bringing the file to **34,920,270 bytes**.
That is our smallest verified enwik8 gzip so far: 7,159 bytes below the
Turtledeflate → unflate result above.

The blocks are joined at matching decoded offsets, preserving their byte history.
The assembled file passes `gzip -t` and decodes byte-for-byte to enwik8. This
combines many compressor runs and lab experiments; `evaluate.py` does not
reproduce the synthesis.

### Canterbury totals

| Baseline | Gzip bytes | Pipeline s | +unflate bytes | Added s | +fast bytes | Added s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| gzip -9 | 730,625 | 0.56 | **672,471** | 9.99 | 729,272 | 1.13 |
| Zopfli --i1 | 677,355 | 8.65 | **670,004** | 11.66 | 676,815 | 1.23 |
| Zopfli --i5 | 670,993 | 10.05 | **668,589** | 9.90 | 670,761 | 1.07 |
| Zopfli --i15 | 669,501 | 13.45 | **667,958** | 11.15 | 669,316 | 1.11 |
| Zopfli --i30 | 668,866 | 18.01 | **667,544** | 10.99 | 668,680 | 1.04 |
| ECT -1 | 727,922 | 0.67 | **672,773** | 10.43 | 726,482 | 1.16 |
| ECT -2 | 691,346 | 1.06 | **679,909** | 33.72 | 689,790 | 3.32 |
| ECT -3 | 690,407 | 1.21 | **679,614** | 33.13 | 689,256 | 3.29 |
| ECT -4 | 684,432 | 1.30 | **679,570** | 34.45 | 683,480 | 3.34 |
| ECT -5 | 680,566 | 1.65 | **678,933** | 32.43 | 679,948 | 3.02 |
| ECT -6 | 678,947 | 2.94 | **677,990** | 31.92 | 678,425 | 2.72 |
| ECT -7 | 677,216 | 3.30 | **676,118** | 31.87 | 676,610 | 2.75 |
| ECT -8 | 673,683 | 5.42 | **672,578** | 33.24 | 673,155 | 2.36 |
| ECT -9 | 673,213 | 7.89 | **672,147** | 33.23 | 672,706 | 2.35 |

### Original defluff and DeflOpt

Each tool starts independently from the same baseline as unflate. “Legacy best”
explores both original executables in every reachable ordering until no new
outputs remain, including equal-size and larger intermediates. It retains the
smallest result, including the baseline. Search time sums every legacy call,
including Wine startup for DeflOpt; verification and working copies are excluded.
Unflate uses one call; its added times are in the tables above. Individual legacy
call times and the winning chains are available in the JSON.

defluff can increase size: its Canterbury totals after ECT levels 3–9 exceed
their baselines, as the italicized results show.

Across these 168 baseline/file combinations, default unflate is strictly smaller
than the exhaustive legacy best every time. Fast mode is smaller in 166 and ties
in two. This is an observation on these inputs, not a guarantee for every stream.

enwik8

| Baseline | +defluff bytes | +DeflOpt bytes | Legacy best bytes | Search s | +unflate bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| gzip -9 | 36,444,728 | 36,444,655 | 36,444,593 | 34.93 | **35,071,629** |
| Zopfli --i1 | 35,095,848 | 35,096,040 | 35,095,823 | 48.69 | **34,991,450** |
| Zopfli --i5 | 34,981,096 | 34,981,203 | 34,981,081 | 31.51 | **34,947,896** |
| Zopfli --i15 | 34,964,329 | 34,964,430 | 34,964,315 | 31.27 | **34,937,279** |
| Zopfli --i30 | 34,959,728 | 34,959,829 | 34,959,715 | 37.44 | **34,934,547** |
| ECT -1 | 36,444,728 | 36,444,655 | 36,444,593 | 34.77 | **35,071,629** |
| ECT -2 | 35,018,694 | 35,018,854 | 35,018,673 | 31.27 | **34,966,755** |
| ECT -3 | 35,014,073 | 35,014,255 | 35,014,057 | 28.78 | **34,956,939** |
| ECT -4 | 34,963,280 | 34,963,471 | 34,963,279 | 14.34 | **34,952,835** |
| ECT -5 | 34,942,735 | 34,942,772 | 34,942,733 | 17.02 | **34,938,802** |
| ECT -6 | 34,943,917 | 34,943,923 | 34,943,915 | 14.10 | **34,940,876** |
| ECT -7 | 34,942,320 | 34,942,326 | 34,942,318 | 14.12 | **34,939,823** |
| ECT -8 | 34,941,088 | 34,941,106 | 34,941,083 | 16.88 | **34,938,773** |
| ECT -9 | 34,937,743 | 34,937,762 | 34,937,737 | 19.62 | **34,935,457** |

Canterbury totals

| Baseline | +defluff bytes | +DeflOpt bytes | Legacy best bytes | Search s | +unflate bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| gzip -9 | 730,165 | 729,989 | 729,970 | 6.44 | **672,471** |
| Zopfli --i1 | 677,111 | 677,107 | 677,097 | 4.66 | **670,004** |
| Zopfli --i5 | 670,965 | 670,954 | 670,952 | 4.44 | **668,589** |
| Zopfli --i15 | 669,465 | 669,456 | 669,451 | 4.80 | **667,958** |
| Zopfli --i30 | 668,828 | 668,819 | 668,816 | 4.75 | **667,544** |
| ECT -1 | 727,446 | 727,269 | 727,245 | 6.57 | **672,773** |
| ECT -2 | 691,138 | 691,253 | 691,118 | 7.21 | **679,909** |
| ECT -3 | *690,567* | 690,360 | 690,357 | 4.92 | **679,614** |
| ECT -4 | *684,682* | 684,411 | 684,405 | 3.95 | **679,570** |
| ECT -5 | *680,925* | 680,553 | 680,553 | 3.67 | **678,933** |
| ECT -6 | *679,252* | 678,941 | 678,941 | 3.46 | **677,990** |
| ECT -7 | *677,401* | 677,165 | 677,165 | 4.63 | **676,118** |
| ECT -8 | *673,736* | 673,622 | 673,622 | 4.29 | **672,578** |
| ECT -9 | *673,244* | 673,138 | 673,138 | 4.81 | **672,147** |
