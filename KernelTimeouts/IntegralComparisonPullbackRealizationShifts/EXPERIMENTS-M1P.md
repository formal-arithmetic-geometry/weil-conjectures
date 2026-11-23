# IntegralComparison M1 propagation (READY4.2)

Fresh O is `IntegralComparisonPullbackRealizationShifts/Before.lean` on
`m1p` revision `105ac3f5b23`, with READY4.2 (`0311a15b5f4`). Root 29958 is
fully aggregated.

| Check | Result |
|---|---:|
| O counters / analyzed calls | 9,426,198 / 9,426,198 |
| Raw entered calls | 3,913 (0.042%) |
| M1 calls / call share | 6,680,842 / 70.875% |
| M1 time share | 99.551% |

M1/M2/Matched time shares are 99.551% / 0.148% / 0.301%. Depth
mean/median/p90/p99/max is 110.610/109/133/155/181; 50% and 90% bands are
97--116 and 82--136. Fan-out mean/median/p90/max is 1.406/1/3/21, giving a
**mixed** verdict. M1 edges are M1->M1 6,672,675, M1->Matched 2,702,845,
and M1->M2 20,527.

The top M1-parent rows cover 93.0% of M1 exclusive time:

| Parent | Child | Branch / kind | Calls | Exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| M1 | M1 | projection / projection | 1,939,881 | 35,631.260 | 1.000 |
| M1 | M1 | application / argument | 1,776,796 | 16,420.633 | 4.019 |
| M1 | M1 | application / function-head | 1,258,057 | 10,211.094 | 2.418 |
| M1 | M1 | second_whnf / whnf-iota-exposure | 481,367 | 6,401.729 | 1.001 |
| M1 | M1 | lazy_delta / argument | 479,374 | 3,563.299 | 8.812 |

Projection to projection remains the dominant M1 transition, matching the
primary case. This light case has no A4 or C intervention.
