# PR2122: M1 propagation (READY4.1)

The original `OriginalRecursor.lean` probe ran under READY4.1 Lean 4.35.0
with a 3600 s limit. Process-wide root 35261 completed with 2,257,184
calls, 15,770.045 ms comparison-exclusive time, and 27,742.749 ms root
wall. A separate fresh counters run measured 2,257,184 calls, 17,611.026 ms
root wall, and 8,138.957 ms comparison-exclusive time. The count equals the
accepted READY3.2 root; M1 exclusive share is 97.330%, 0.067 percentage
points below its reference share. Analyzer: READY4.1 `mprwe_analyze.py`,
kernel dataset commit `5ae674db0c7`.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.044 | <0.001% |
| M1 | 1,797,805 | 15,349.042 | 97.330% |
| M2 | 51,859 | 381.866 | 2.421% |
| Matched | 406,401 | 27.237 | 0.173% |
| Unclassified | 1,118 | 11.855 | 0.075% |

Aggregate coverage is 2,257,184/2,257,184 calls; raw capture is 1,477
entered and 1,424 exited calls (0.0654% by entered calls). The complete
2,257,183 transition edges plus 0.044 ms root direct time reconcile to
the root. Every label's depth calls and exclusive/reduction times match
its aggregates; no depths were clamped. READY4.1 does not emit a complete
parent-label by child-label edge matrix.

## A2: depth and fan-out

M1 depth mean 49.311, median 50, p90 60, p99 70, max 87. The narrowest
depth bands containing 50% and 90% of M1 exclusive time are 46-58 and
32-64. Ten-depth histogram (start: calls/exclusive ms): 0:413/5.2;
10:1,806/18.6; 20:24,106/224.1; 30:217,550/1,662.1;
40:649,131/4,908.2; 50:690,087/5,935.8;
60:193,816/2,115.4; 70:20,426/371.3; 80:470/108.3.

M1-parent fan-out over all child labels: mean 1.219, median 1, p90 3,
max 21. Exact histogram (children:nodes): 0:634,417; 1:676,468;
2:218,446; 3:149,131; 4:83,252; 5:1,335; 6:6,489;
7:16,030; 8:4,537; 9:3,099; 10:353; 11:5; 14:2,526;
16:1; 21:1,716. The bounded raw window observes 1,149 M1-to-M1,
245 M1-to-Matched, and 29 M1-to-M2 edges; these are sample counts.

This is **mixed** propagation: the 40-60 depth range carries most M1
time, with projection and application branches providing repeated fan-out.
The highest named M1 path bucket is the `argument[1]/argument[0]/argument[7]`
continuation (660,553 calls; 6,957.768 ms); the next named bucket begins
`argument[2]/argument[0]/argument[7]` (142,516 calls; 1,222.280 ms).
Each `*` bucket groups deeper paths, not one inclusive subtree.

## A3: transition matrix

Rows include every child label. The first five hold 14,857.688 ms,
94.2% of root exclusive time; subtracting all non-M1 time still leaves
over 90% of M1 time in those rows. Mean fan-out by parent branch is not
emitted; the complete M1-parent mean is above.

| Parent branch | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 496,679 | 6,418.327 |
| application | argument | 863,194 | 4,723.242 |
| second_whnf | fallback | 169,846 | 2,207.670 |
| application | function-head | 431,750 | 941.235 |
| quick | dependent-body | 40,583 | 567.214 |
| lazy_delta | argument | 106,622 | 450.863 |
| proof_irrelevance | proposition-type | 34,374 | 351.160 |
| remaining rows | mixed | 114,135 | 110.290 |

The top rows are the application, projection, and WHNF branches in the
exact 4.35.0 `type_checker.cpp` source (`M1P-KERNEL.md`, lines 1628, 1857,
and 1909). The matrix is complete for cost but not split by provenance.
