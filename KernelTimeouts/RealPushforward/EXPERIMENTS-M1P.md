# RealPushforward M1 propagation (READY4.2)

The three fresh O repeats use `RealPushforward/Before.lean` from `m1p`
revision `105ac3f5b23`, with READY4.2 (`0311a15b5f4`). Root 2005 reaches the
expected deterministic timeout after complete aggregate capture.

| Repeat result | Value |
|---|---:|
| O counters / analyzed calls | 17,340,236 / 17,340,236 (all repeats) |
| Raw entered calls | 3,122 (0.018%) per repeat |
| M1 calls / call share | 8,002,209 / 46.148% |
| M1 time share | 61.446% [61.312--63.086%] |
| M2 / Matched median time shares | 37.303% / 1.250% |

Root and label call counts match READY4.1. Aggregate coverage is complete;
raw records are only the bounded review sample.

## A2/A3

M1 depth mean/median/p90/p99/max is 83.865/84/86/88/89. The 50% and 90%
bands are 82--84 and 74--87. Fan-out mean/median/p90/max is 1.274/1/1/18.
The analyzer verdict is **deep**. M1 edges are M1->M1 6,502,766,
M1->Matched 1,698,481, and M1->M2 1,990,961.

The rows below cover 93.2% of M1 exclusive time; parent=M2 rows expose the
M1 children below the large M2 branch.

| Parent | Child | Branch / kind | Calls | Exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| M1 | M1 | projection / projection | 4,294,654 | 19,423.987 | 1.000 |
| M2 | M1 | quick / dependent-body | 957,710 | 18,592.956 | 1.000 |
| M1 | M1 | quick / dependent-body | 501,963 | 12,847.939 | 1.000 |
| M2 | M1 | application / argument | 540,587 | 8,195.500 | 8.802 |
| M1 | M1 | application / argument | 274,594 | 6,103.110 | 9.227 |

Projection to projection remains the dominant M1 transition, matching
EtaleHom despite the large M2 share. C was not requested for this control.
