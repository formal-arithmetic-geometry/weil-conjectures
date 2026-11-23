# F66Adj M1 propagation (READY4.2)

Fresh O is `F66Adj/probes/mprwe/Original.lean` on the `m1p` import revision
`105ac3f5b23`, with READY4.2 (`0311a15b5f4`) Lean 4.35.0. Root 6122 is
analyzed completely.

| Check | Result |
|---|---:|
| O counters / analyzed calls | 3,897,905 / 3,897,905 |
| Raw entered calls | 3,685 (0.095%) |
| M1 calls / call share | 2,961,163 / 75.968% |
| M1 time share | 99.803% |

The complete aggregate is the source of all labels and distributions; raw
records are only for manual inspection. M1/M2/Matched time shares are
99.803% / 0.000% / 0.197%.

## A2/A3

Depth mean/median/p90/p99/max is 89.227/90/102/110/121; the 50% and 90%
bands are 85--98 and 74--107. Fan-out mean/median/p90/max is 1.316/1/3/28.
The analyzer verdict is **mixed** because the deep predicate holds while the
90%-time band is wider than 32 levels. M1 edges are M1->M1 2,961,160,
M1->Matched 936,731, M1->M2 9.

The top M1-parent rows cover 95.5% of M1 exclusive time:

| Parent | Child | Branch / kind | Calls | Exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| M1 | M1 | projection / projection | 761,198 | 17,619.913 | 1.000 |
| M1 | M1 | application / argument | 862,146 | 8,223.611 | 3.905 |
| M1 | M1 | second_whnf / whnf-iota-exposure | 310,389 | 4,251.405 | 1.000 |
| M1 | M1 | application / function-head | 545,965 | 3,558.777 | 2.506 |
| M1 | M1 | quick / dependent-body | 89,318 | 1,998.116 | 2.978 |

Projection descent is the dominant M1 transition, matching EtaleHom. This
light case has no A4 or C intervention.
