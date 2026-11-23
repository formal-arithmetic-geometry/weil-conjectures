# PR1556: M1 propagation (READY4.2)

## Validation

The fresh original `OriginalNatTrans.lean` probe ran with the READY4.2
Lean 4.35.0 binary and root 6006. The analyzed root has 6,670,198 calls;
the separate counters run has the same 6,670,198 calls. The accepted
READY3.2 count was also 6,670,198. M1 is 5,006,059 calls (75.051% of
calls) and 99.707% of comparison-exclusive time, within 0.5 percentage
points of READY4.1 (99.671%).

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.052 | 0.000% |
| M1 | 5,006,059 | 56,520.661 | 99.707% |
| M2 | 9,121 | 42.157 | 0.074% |
| Matched | 1,655,017 | 123.903 | 0.219% |
| Unclassified | 0 | 0 | 0.000% |

Analyzer: READY4.2 `mprwe_analyze.py`, kernel dataset commit
`0311a15b5f4`. Aggregate coverage is 6,670,198/6,670,198 calls; raw
capture is 1,499 entered and 1,429 exited calls (0.0225%). The aggregate
matrix and label times are complete and reconcile to 6,670,197 child edges
plus 0.052 ms root-direct time. No depth was clamped.

## A2: topology

M1 depth mean/median/p90/p99/max is 133.587/122/181/193/213. The narrowest
bands containing 50% and 90% of M1 exclusive time are 87-125 and 89-187.
M1-parent fan-out mean/median/p90/max is 1.330/1/3/21. M1 -> M1,
M1 -> Matched, and M1 -> M2 edge counts are 5,003,086, 1,649,139, and
7,606. The analyzer verdict is **mixed**: the lineage is deep, while
application and projection parents repeatedly branch.

## A3: M1-parent transition matrix

The first seven M1-parent rows below account for 99.0% of M1 exclusive
time. `failure` is retained only as `parent_outcome`; it is not a branch.

| Initiating branch | Child kind | Child label | Calls | Child exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| projection | projection | M1 | 1,289,253 | 24,136.670 | 1.000 |
| application | argument | M1 | 1,477,956 | 15,028.210 | 3.923 |
| second_whnf | whnf-iota-exposure | M1 | 542,684 | 7,637.933 | 1.000 |
| application | function-head | M1 | 932,066 | 3,883.365 | 2.511 |
| quick | dependent-body | M1 | 157,461 | 3,206.558 | 2.758 |
| proof_irrelevance | proposition-type | M1 | 126,864 | 1,457.069 | 1.000 |
| lazy_delta | argument | M1 | 199,969 | 1,079.109 | 9.243 |

The dominant transition remains projection descent after provenance is
split by child label. The largest non-M1 rows are application-argument
M1 -> Matched (1,182,475 calls, 94.243 ms) and eta-structure M1 -> M2
(1,496 calls, 29.154 ms).

## A4: first transitions

The READY4.2 matrix leaves the READY4.1 manual reconstruction unchanged.
The root pair is `Eq`/`Eq`; its function-head child is Matched, while the
`Quiver.Hom` application argument enters M1. The next application argument
compares `CategoryStruct.comp` with itself and enters the M2 branch after
reduction. The M1 continuation descends through `DFunLike.coe`, an
`Equiv.proj` function head, and `equivShrink` projection components. Each
child retains the parent divergence hashes, so it remains in the M1
lineage. These calls are issued by application congruence and
`lazy_delta_proj_reduction` in the audited `type_checker.cpp` branches
(`M1P-KERNEL.md`, `is_def_eq_app` and `lazy_delta_proj_reduction`).

## C: M0-preserving cut point

The selected major-premise continuation still has no type-correct local
replacement at the original dependent type. The available alignment changes
the inferred domain and removes M0, so no valid O-cut/O-restore comparison
exists. C remains blocked by the dependent domain.
