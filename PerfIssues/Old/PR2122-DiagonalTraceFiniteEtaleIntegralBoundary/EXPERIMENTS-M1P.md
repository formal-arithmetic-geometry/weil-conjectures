# PR2122: M1 propagation (READY4.2)

The fresh original `OriginalRecursor.lean` READY4.2 run selected root
35261. Counters and analyzed trace both have 2,257,184 calls, equal to
READY3.2. M1 has 1,797,805 calls (79.648% of calls) and 98.113% of
exclusive time. This is 0.783 percentage points above READY4.1 (97.330%);
the unchanged call total and complete READY4.2 matrix show that this is the
small tail's corrected provenance split: M2 falls by 0.711 points, with the
remaining shift in Matched and Unclassified time. The READY4.2 result is
the one used below.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.057 | 0.000% |
| M1 | 1,797,805 | 23,214.127 | 98.113% |
| M2 | 51,859 | 404.706 | 1.710% |
| Matched | 406,401 | 27.563 | 0.116% |
| Unclassified | 1,118 | 14.051 | 0.059% |

Analyzer: READY4.2 `mprwe_analyze.py`, kernel dataset commit
`0311a15b5f4`. Aggregate coverage is 2,257,184/2,257,184 calls; raw
capture is 1,477 entered and 1,424 exited calls (0.0654%). The complete
matrix reconciles to 2,257,183 child edges plus 0.057 ms root-direct time.

## A2: topology

M1 depth mean/median/p90/p99/max is 49.311/50/60/70/87. The narrowest
bands containing 50% and 90% of M1 exclusive time are 42-54 and 36-65.
M1-parent fan-out mean/median/p90/max is 1.219/1/3/21. M1 -> M1,
M1 -> Matched, and M1 -> M2 edges are 1,753,186, 384,748, and 51,716.
The analyzer verdict is **mixed**.

## A3: M1-parent transition matrix

The first seven rows cover 99.0% of M1 exclusive time.

| Initiating branch | Child kind | Child label | Calls | Child exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| projection | projection | M1 | 438,048 | 11,533.470 | 1.000 |
| application | argument | M1 | 559,515 | 5,294.064 | 3.675 |
| second_whnf | whnf-iota-exposure | M1 | 166,910 | 2,908.458 | 1.000 |
| application | function-head | M1 | 298,093 | 1,239.419 | 2.408 |
| quick | dependent-body | M1 | 40,399 | 932.470 | 2.807 |
| lazy_delta | argument | M1 | 140,931 | 644.881 | 4.532 |
| proof_irrelevance | proposition-type | M1 | 34,048 | 388.603 | 1.000 |

Projection descent remains dominant. The main non-M1 continuation is
projection M1 -> M2 (36,196 calls, 333.716 ms), followed by application
argument M1 -> Matched (268,183 calls, 18.558 ms).

Aggregate coverage is complete despite the bounded raw window. This light
case has no assigned C intervention.
