# ImageHomCounit M1 propagation (READY4.2)

Fresh O is `ImageHomCounit/probes/mprwe/Original.lean` on `m1p` revision
`105ac3f5b23`, using READY4.2 (`0311a15b5f4`). Root 2129 has complete
aggregate coverage.

| Check | Result |
|---|---:|
| O counters / analyzed calls | 6,359,958 / 6,359,958 |
| Raw entered calls | 3,773 (0.059%) |
| M1 calls / call share | 4,781,271 / 75.178% |
| M1 time share | 99.768% |

M1/M2/Matched time shares are 99.768% / 0.008% / 0.224%. The analyzer
classifies the propagation as **deep**: depth mean/median/p90/p99/max is
161.655/162/173/180/204, 50% and 90% bands are 155--167 and 148--177,
and fan-out mean/median/p90/max is 1.330/1/3/28.

M1 edges are M1->M1 4,781,165, M1->Matched 1,578,192, and M1->M2 157.
The following M1-parent rows cover 95.3% of M1 exclusive time:

| Parent | Child | Branch / kind | Calls | Exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| M1 | M1 | projection / projection | 1,253,593 | 22,455.792 | 1.000 |
| M1 | M1 | application / argument | 1,399,602 | 13,821.867 | 3.923 |
| M1 | M1 | second_whnf / whnf-iota-exposure | 511,355 | 7,705.421 | 1.000 |
| M1 | M1 | application / function-head | 898,759 | 3,443.045 | 2.506 |
| M1 | M1 | quick / dependent-body | 147,031 | 3,062.933 | 2.806 |

The dominant M1 transition is projection to projection, the same strategy as
EtaleHom. This light case has no A4 or C intervention.
