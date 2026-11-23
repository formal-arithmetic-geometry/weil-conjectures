# PR1563: M1 propagation (READY4.2)

The fresh original `OriginalComposition.lean` READY4.2 run selected root
7269. Counters and analyzed trace both have 2,563,145 calls, equal to
READY3.2. M1 has 1,924,504 calls (75.084% of calls) and 99.731% of
exclusive time, within 0.5 percentage points of READY4.1 (99.617%).

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.054 | 0.000% |
| M1 | 1,924,504 | 26,222.543 | 99.731% |
| M2 | 1,029 | 12.429 | 0.047% |
| Matched | 637,607 | 58.167 | 0.221% |
| Unclassified | 4 | 0.095 | 0.000% |

Analyzer: READY4.2 `mprwe_analyze.py`, kernel dataset commit
`0311a15b5f4`. Aggregate coverage is 2,563,145/2,563,145 calls; raw
capture is 1,748 entered and 1,706 exited calls (0.0682%). The complete
matrix reconciles to 2,563,144 child edges plus 0.054 ms root-direct time.

## A2: topology

M1 depth mean/median/p90/p99/max is 56.560/57/70/80/93. The narrowest
bands containing 50% and 90% of M1 exclusive time are 51-63 and 40-73.
M1-parent fan-out mean/median/p90/max is 1.331/1/3/21. M1 -> M1,
M1 -> Matched, and M1 -> M2 edges are 1,924,060, 637,204, and 773.
The analyzer verdict is **mixed**.

## A3: M1-parent transition matrix

The first seven rows cover 99.3% of M1 exclusive time.

| Initiating branch | Child kind | Child label | Calls | Child exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| projection | projection | M1 | 503,517 | 12,829.237 | 1.000 |
| application | argument | M1 | 563,921 | 5,631.705 | 3.931 |
| second_whnf | whnf-iota-exposure | M1 | 206,441 | 2,990.115 | 1.000 |
| application | function-head | M1 | 360,666 | 1,744.344 | 2.507 |
| quick | dependent-body | M1 | 59,392 | 1,512.890 | 2.796 |
| proof_irrelevance | proposition-type | M1 | 48,950 | 723.254 | 1.000 |
| lazy_delta | argument | M1 | 74,514 | 623.390 | 10.156 |

The dominant M1 transition is projection descent. Its largest non-M1
continuations are application-argument M1 -> Matched (459,647 calls,
40.426 ms) and lazy-delta argument M1 -> Matched (63,840 calls, 9.335 ms).

Aggregate coverage is complete despite the bounded raw window. This light
case has no assigned C intervention.
