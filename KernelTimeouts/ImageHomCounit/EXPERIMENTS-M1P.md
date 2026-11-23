# ImageHomCounit M1 propagation (READY4.1)

Fresh O is `probes/mprwe/Original.lean` on Lean 4.35.0, current import
revision `15b8acba63e`, READY4.1 kernel/analyzer revision `5ae674db0c7`.
The expensive original root is 2129. O counters and analyzed root both
record 6,359,958 calls, exactly the accepted READY3.2 count. Counter root
wall/comparison/reduction are 50,210.252/26,200.319/24,009.934 ms;
trace comparison exclusive is 54,548.360 ms. Aggregate coverage is
6,359,958/6,359,958; raw entered coverage is 3,773/6,359,958 (0.059%).
The aggregate labels and depth rows include calls absent from raw capture.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.277 | 0.001% |
| M1 | 4,781,271 | 54,425.328 | 99.774% |
| M2 | 276 | 4.126 | 0.008% |
| Matched | 1,578,409 | 118.605 | 0.217% |
| Unclassified | 1 | 0.024 | 0.000% |

The M1 share is within 0.5 percentage points of the accepted READY3.2
share. The extra observational bookkeeping affects time but the
recursive call count is unchanged.

## A2: depth and fan-out

M1 depth mean/median/p90/p99/max is 161.655/162/173/180/204.
The narrowest 50% and 90% M1 exclusive-time bands are 154--166 and
146--175. M1 fan-out mean/median/p90/max is 1.330/1/3/28.
Its count histogram is 0: 1,535,798; 1: 1,899,224; 2: 510,668;
3: 487,876; 4--9: 314,519; 10+: 33,186. No depth was clamped.
This is mixed deep/wide propagation: its cost sits particularly deep,
while repeated branching reaches 28 children. In the bounded raw sample,
M1 parents have 2,032 M1, 1,409 Matched, and 68 M2 child edges;
whole-root label-to-label edge counts are not emitted.

## A3: transition matrix

The five largest complete-root rows account for 52,058.269 ms, at least
95.4% of M1 time even if all non-M1 time were assigned to these rows.
The rows cover all labels; READY4.1 does not emit per-row M1 counts or
per-row mean child fan-out.

| Parent | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 1,253,595 | 24,567.495 |
| application | argument | 2,536,712 | 13,532.243 |
| second_whnf | fallback | 511,395 | 7,627.285 |
| application | function-head | 1,178,468 | 3,726.102 |
| quick | dependent-body | 145,091 | 2,605.144 |

The transition matrix has 6,359,957 child calls, equal to the root calls
minus one. Projection descent is largest. Sampled costly M1 heads include
`DerivedCategory.tensorHomAdjunctionQhObj`,
`DerivedCategory.instMonoidalCategory._aux_5`, and `DFunLike.coe`.
This light case does not include A4 or C.
