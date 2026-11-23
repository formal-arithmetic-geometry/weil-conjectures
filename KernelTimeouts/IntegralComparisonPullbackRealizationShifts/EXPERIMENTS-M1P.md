# IntegralComparison M1 propagation (READY4.1)

Fresh O is the full `Before.lean` source, not the smaller
`probes/mprwe/Original.lean` diagnostic. It uses Lean 4.35.0, current
import revision `15b8acba63e`, and READY4.1 kernel/analyzer revision
`5ae674db0c7`. The expensive original root is 29958. O counters and
analyzed root both record 9,426,198 calls, exactly the accepted READY3.2
count. Counter root wall/comparison/reduction are
93,396.718/57,751.548/35,645.170 ms; trace comparison exclusive is
81,353.889 ms. Aggregate coverage is 9,426,198/9,426,198; raw entered
coverage is 3,913/9,426,198 (0.042%). Complete label and depth
aggregates are independent of the bounded raw capture.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.034 | 0.000% |
| M1 | 6,680,842 | 81,002.764 | 99.568% |
| M2 | 25,198 | 112.185 | 0.138% |
| Matched | 2,720,157 | 238.905 | 0.294% |
| Unclassified | 0 | 0.000 | 0.000% |

M1's time share is within 0.5 percentage points of the accepted
READY3.2 share. The root and label call counts are unchanged;
READY4.1's added observational bookkeeping changes measured exclusive
time. Counter and trace time are separate runs.

## A2: depth and fan-out

M1 depth mean/median/p90/p99/max is 110.610/109/133/155/181.
The narrowest 50% and 90% M1 exclusive-time bands are 93--113 and
83--138. M1 fan-out mean/median/p90/max is 1.406/1/3/21.
Its count histogram is 0: 2,058,264; 1: 2,638,442; 2: 816,234;
3: 600,494; 4--9: 520,404; 10+: 47,004. No depth was clamped.
This is mixed deep/wide propagation: expensive comparisons extend well
past depth 100, with repeated argument/projection fan-out. In the
bounded raw sample, M1 parents have 2,262 M1, 1,608 Matched, and 11 M2
child edges. These are sample counts, not whole-root label-edge totals.

## A3: transition matrix

The five largest complete-root rows total 75,395.658 ms. Even if all
351.125 ms of non-M1 time fell in these rows, they still contain at
least 92.6% of M1 time. READY4.1 does not emit label-specific row counts
or row mean fan-out.

| Parent | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 1,939,604 | 38,679.727 |
| application | argument | 3,396,407 | 16,247.625 |
| application | function-head | 1,664,477 | 10,255.058 |
| second_whnf | fallback | 481,388 | 6,383.487 |
| quick | dependent-body | 207,458 | 3,829.761 |

The matrix has 9,426,197 child calls, equal to the root count minus one.
Projection descent is the largest complete-root row. The costly raw M1
sample repeatedly reaches `PresheafOfModules.proj`.
This light case does not include A4 or C.
