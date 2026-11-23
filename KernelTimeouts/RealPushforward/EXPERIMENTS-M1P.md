# RealPushforward M1 propagation (READY4.1)

Fresh O is the full `Before.lean` source on Lean 4.35.0, current import
revision `15b8acba63e`, READY4.1 kernel/analyzer revision `5ae674db0c7`.
The expensive original root is 2005. O counters and analyzed root both
record 17,340,236 calls, exactly the accepted READY3.2 count. Counter
root wall/comparison/reduction are 59,267.968/59,265.094/2.874 ms;
trace comparison exclusive is 93,214.215 ms. Aggregate coverage is
17,340,236/17,340,236; raw entered coverage is 3,122/17,340,236
(0.018%). The deterministic kernel timeout is the expected O outcome.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.021 | 0.000% |
| M1 | 8,002,209 | 58,086.434 | 62.315% |
| M2 | 4,364,762 | 34,071.861 | 36.552% |
| Matched | 4,973,262 | 1,055.871 | 1.133% |
| Unclassified | 2 | 0.027 | 0.000% |

M1's time share differs from the accepted READY3.2 share by more than
0.5 percentage points, though every provenance call count and the root count match.
The time-share difference is exclusively measured time weighting,
consistent with READY4.1's additional branch/depth bookkeeping and
run-to-run variation in the mixed failure/projection path. It is not
a changed root. Counter and trace times are separate runs.

## A2: depth and fan-out

M1 depth mean/median/p90/p99/max is 83.865/84/86/88/89.
The narrowest 50% and 90% M1 exclusive-time bands are 82--84 and
79--87. M1 fan-out mean/median/p90/max is 1.274/1/1/18.
Its count histogram is 0: 69,232; 1: 7,658,286; 2: 129;
3: 79; 4--9: 95,644; 10+: 178,839. No depth was clamped.
This is mixed propagation: most nodes extend a deep unary chain, while
178,839 nodes have ten or more children. In the bounded raw sample,
M1 parents have 1,363 M1, 376 Matched, and 304 M2 child edges;
these are not whole-root label-edge totals.

## A3: transition matrix

The five largest complete-root rows total 90.444 s. Even if all
35,127.781 ms of non-M1 time fell in those rows, they still contain at
least 95.2% of M1 time. READY4.1 does not emit label-specific row counts
or row mean fan-out.

| Parent outcome/branch | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| failure | projection | 7,157,257 | 33,623.025 |
| lazy_delta | dependent-body | 1,430,736 | 21,625.442 |
| failure | field | 2,864,586 | 19,070.038 |
| failure | argument | 3,542,981 | 11,594.005 |
| failure | function-head | 2,245,822 | 4,531.172 |

The transition matrix has 17,340,235 child calls, equal to root calls
minus one. `failure` records the parent's final outcome, so these rows
do not by themselves identify the branch that initiated the child.
The Cone and EtaleHom primary roots have projection descent as their
largest complete-root row; NativePullTensor emphasizes application
congruence (`M1P-KERNEL.md`). This mixed root's largest row is
failure-to-projection and its M2 share is 36.552%. The raw sample retains
projection and argument M1 children, but the M1-only dominant kernel
strategy cannot be established from the unlabeled complete-root rows.
