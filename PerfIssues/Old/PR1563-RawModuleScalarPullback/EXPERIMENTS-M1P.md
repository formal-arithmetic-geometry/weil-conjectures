# PR1563: M1 propagation (READY4.1)

The original `OriginalComposition.lean` probe ran under READY4.1 Lean 4.35.0
with a 3600 s limit. Process-wide root 7269 completed with 2,563,145 calls,
17,628.036 ms comparison-exclusive time, and 29,279.407 ms root wall.
The separate fresh counters run measured 2,563,145 calls, 21,048.567 ms
root wall, and 10,656.709 ms comparison-exclusive time. The count equals the accepted
READY3.2 root; M1 exclusive share is 99.617%, 0.064 percentage points above
that round's reference share. Analyzer: READY4.1 `mprwe_analyze.py`, kernel
dataset commit `5ae674db0c7`.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.068 | <0.001% |
| M1 | 1,924,504 | 17,560.483 | 99.617% |
| M2 | 1,029 | 11.141 | 0.063% |
| Matched | 637,607 | 56.259 | 0.319% |
| Unclassified | 4 | 0.085 | <0.001% |

Aggregate coverage is 2,563,145/2,563,145 calls; raw capture is 1,748
entered and 1,706 exited calls (0.0682% by entered calls). The complete
2,563,144 transition edges plus 0.068 ms root direct time reconcile to
the root total. Per-label depth calls and exclusive/reduction times equal
their aggregates; no depths were clamped. The complete label-by-label edge
matrix is unavailable in the unchanged READY4.1 patch.

## A2: depth and fan-out

M1 depth mean 56.560, median 57, p90 70, p99 80, max 93. The narrowest
depth bands containing 50% and 90% of M1 exclusive time are 49-62 and
38-72. Ten-depth histogram (start: calls/exclusive ms): 0:452/7.1;
10:1,468/17.1; 20:8,305/94.6; 30:86,068/774.7;
40:373,008/3,234.4; 50:697,042/6,418.4;
60:559,944/5,149.9; 70:178,789/1,670.6;
80:19,328/193.3; 90:100/0.5.

M1-parent fan-out over all child labels: mean 1.331, median 1, p90 3,
max 21. Exact histogram (children:nodes): 0:618,084; 1:764,638;
2:204,777; 3:196,500; 4:99,198; 5:3,072; 6:12,822;
7:9,584; 8:184; 9:2,621; 10:310; 11:27; 12:13;
13:5; 14:7,506; 15:1; 18:1; 20:1; 21:5,160.
The bounded raw window observes 848 M1-to-M1, 348 M1-to-Matched,
and 324 M1-to-M2 edges; these are not complete edge totals.

This is **mixed** propagation: most M1 time is at depths 40-70 while
projection and application comparisons repeatedly branch. The top named
M1 buckets are the `argument[2]/argument[7]/argument[6]/projection`
continuation (426,606 calls; 3,725.507 ms) and the
`argument[2]/argument[6]/argument[5]` continuation (213,986 calls;
2,174.762 ms); the buckets group deeper `*` paths.

## A3: transition matrix

Rows include every child label. The first five hold 16,746.644 ms,
95.0% of root exclusive time; even attributing all non-M1 time to them
leaves over 90% of M1 time. Mean fan-out by branch is not emitted by the
patch; the M1-parent mean above is complete.

| Parent branch | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 503,599 | 7,040.628 |
| application | argument | 1,024,017 | 5,008.828 |
| second_whnf | fallback | 206,657 | 2,385.308 |
| application | function-head | 474,300 | 1,262.869 |
| quick | dependent-body | 58,642 | 1,049.011 |
| proof_irrelevance | proposition-type | 49,074 | 499.773 |
| lazy_delta | argument | 127,182 | 298.709 |
| remaining rows | mixed | 119,673 | 82.842 |

The top rows correspond to `is_def_eq_app`, projection reduction, and
second WHNF fallback in the exact 4.35.0 `type_checker.cpp` source
(`M1P-KERNEL.md`, lines 1628, 1857, and 1909). Their exclusive cost is
complete, but the matrix does not split rows by M1/M2/Matched.
