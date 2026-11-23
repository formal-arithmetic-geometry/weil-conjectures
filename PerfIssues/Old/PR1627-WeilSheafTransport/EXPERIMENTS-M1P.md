# PR1627 control: M1 propagation (READY4.2)

## Validation and repeats

Three fresh original `OriginalGeneratedFields.lean` READY4.2 traces use
root 15228. Each has 10,904,899 calls, matching the separate counters run
and READY3.2. M1 has 2,619,482 calls (24.021% of calls). The three M1
exclusive-time shares are 64.767%, 64.067%, and 65.217%; the reported
median is 64.767% with a 64.1-65.2 percentage-point spread. The median is
1.254 points above the single READY4.1 share (63.513%), while calls and all
provenance-keyed edge counts are identical; the repeat spread explains the
timing difference.

| Label | Calls | Exclusive ms (repeat 1) | Share (repeat 1) |
|---|---:|---:|---:|
| M0 | 1 | 0.033 | 0.000% |
| M1 | 2,619,482 | 21,873.258 | 64.767% |
| M2 | 1,512,663 | 8,340.435 | 24.690% |
| Matched | 6,772,753 | 3,558.497 | 10.538% |
| Unclassified | 0 | 0 | 0.000% |

Analyzer: READY4.2 `mprwe_analyze.py`, kernel dataset commit
`0311a15b5f4`. Aggregate coverage is 10,904,899/10,904,899 calls; each
raw window contains 1,518 entered and 1,479 exited calls (0.0139%). The
complete matrix reconciles to 10,904,898 child edges plus 0.033 ms root
direct time. No depth was clamped.

## A2: topology

M1 depth mean/median/p90/p99/max is 33.464/34/37/50/61. The 50% band is
29-35 in the median repeat (the repeat range is 29-35); the 90% band is
24-37. M1-parent fan-out mean/median/p90/max is 2.037/0/9/18. M1 -> M1,
M1 -> Matched, and M1 -> M2 edges are 1,180,833, 2,662,551, and
1,492,777. The analyzer verdict is **wide**.

## A3: M1-parent transition matrix and Matched work

The first six rows account for the principal M1-parent cost. `failure` is
only a parent outcome; the initiating branch for the fallback row is
`unattributed`, which is recorded as an instrumentation gap rather than
renamed to an outcome.

| Initiating branch | Child kind | Child label | Calls | Child exclusive ms (repeat 1) | Mean fan-out |
|---|---|---|---:|---:|---:|
| quick | dependent-body | M1 | 482,548 | 8,807.387 | 1.000 |
| application | argument | M1 | 639,487 | 7,284.632 | 7.503 |
| unattributed | fallback | M2 | 1,331,712 | 6,798.695 | 9.000 |
| application | argument | Matched | 1,935,770 | 3,163.185 | 7.528 |
| eta_structure | field | M2 | 161,025 | 1,108.080 | 13.107 |
| projection | projection | M1 | 48,446 | 478.030 | 1.058 |

Matched accounts for 6,772,753 calls but only 10.538% of exclusive time.
The 1,935,770 application-argument M1 -> Matched children share the same
generated-field application path as the M1 continuation; the Matched side
comparisons are numerous and cheap while the M1 dependent-body and
application branches carry the expensive lineage.

## A4 and C

This is the mixed control, so no primary-case manual path reconstruction or
C intervention is assigned. The READY4.2 matrix corrects the earlier
outcome-as-branch display and makes the Matched adjacency explicit.
