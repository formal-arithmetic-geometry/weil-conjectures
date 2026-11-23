# F66Adj M1 propagation (READY4.1)

Fresh O is `probes/mprwe/Original.lean` on Lean 4.35.0, current import
revision `15b8acba63e`, READY4.1 kernel/analyzer revision `5ae674db0c7`.
The expensive original root is 6122. O counters and analyzed root both
record 3,897,905 calls, exactly the accepted READY3.2 count. Counter root
wall/comparison/reduction are 31,976.533/16,657.328/15,319.206 ms;
trace comparison exclusive is 26,477.787 ms. Aggregate coverage is
3,897,905/3,897,905; raw entered coverage is 3,685/3,897,905 (0.095%).
The raw cap does not limit the complete aggregate labels or depth rows.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.026 | 0.000% |
| M1 | 2,961,163 | 26,404.101 | 99.722% |
| M2 | 9 | 0.052 | 0.000% |
| Matched | 936,732 | 73.608 | 0.278% |
| Unclassified | 0 | 0.000 | 0.000% |

The M1 share is within 0.5 percentage points of the accepted READY3.2
share. The root operation and recursive call count are unchanged;
the extra observational bookkeeping changes measured exclusive time.

## A2: depth and fan-out

M1 depth mean/median/p90/p99/max is 89.227/90/102/110/121.
The narrowest 50% and 90% M1 exclusive-time bands are 82--96 and
72--106. M1 fan-out mean/median/p90/max is 1.316/1/3/28.
Its count histogram is 0: 982,609; 1: 1,145,484; 2: 317,809;
3: 300,097; 4--9: 194,926; 10+: 20,238. No depth was clamped.
This is mixed deep/wide propagation: a long M1 chain repeatedly opens
argument and projection children. In the bounded raw sample, M1 parents
have 2,820 M1, 859 Matched, and 2 M2 child edges; whole-root
label-to-label edge counts are not emitted.

## A3: transition matrix

The five largest complete-root rows account for 25,060.315 ms, at least
94.6% of M1 time after allowing all non-M1 time to fall in these rows.
The rows cover all labels; READY4.1 does not emit per-row M1 counts or
per-row mean child fan-out.

| Parent | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 761,198 | 10,436.177 |
| application | argument | 1,544,582 | 7,325.609 |
| second_whnf | fallback | 310,390 | 3,736.506 |
| application | function-head | 719,539 | 1,977.442 |
| quick | dependent-body | 88,142 | 1,584.581 |

The transition matrix has 3,897,904 child calls, equal to the root calls
minus one. Projection descent is the largest row, with application
argument comparison next. The sampled high-cost M1 heads include
`DFunLike.coe`, `Functor.proj`, and `MonoidalCategoryStruct.tensorObj`.
This light case does not include A4 or C.
