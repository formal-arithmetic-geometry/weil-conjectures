# PR1624: M1 propagation (READY4.2)

## Validation

The fresh original `OriginalDependentEndpoint.lean` probe ran with the
READY4.2 Lean 4.35.0 flags and root 22078. The analyzed root and counters
run each have 6,598,545 calls, equal to READY3.2. M1 is 5,215,138 calls
(79.035% of calls) and 99.848% of comparison-exclusive time, within 0.5
percentage points of READY4.1 (99.782%).

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.054 | 0.000% |
| M1 | 5,215,138 | 63,577.648 | 99.848% |
| M2 | 287 | 3.355 | 0.005% |
| Matched | 1,383,111 | 93.371 | 0.147% |
| Unclassified | 8 | 0.296 | 0.000% |

Analyzer: READY4.2 `mprwe_analyze.py`, kernel dataset commit
`0311a15b5f4`. Aggregate coverage is 6,598,545/6,598,545 calls; raw
capture is 1,483 entered and 1,406 exited calls (0.0225%). The complete
matrix reconciles to 6,598,544 child edges plus 0.054 ms root-direct time.
No depth was clamped.

## A2: topology

M1 depth mean/median/p90/p99/max is 59.312/60/70/77/88. The narrowest
bands containing 50% and 90% of M1 exclusive time are 57-68 and 46-74.
M1-parent fan-out mean/median/p90/max is 1.265/1/3/21. M1 -> M1,
M1 -> Matched, and M1 -> M2 edge counts are 5,214,946, 1,382,892, and
193. The analyzer verdict is **mixed** under the common rule.

## A3: M1-parent transition matrix

The first seven rows cover 99.0% of M1 exclusive time.

| Initiating branch | Child kind | Child label | Calls | Child exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| projection | projection | M1 | 1,296,250 | 30,977.028 | 1.000 |
| application | argument | M1 | 1,592,155 | 14,707.319 | 3.928 |
| second_whnf | whnf-iota-exposure | M1 | 533,566 | 6,891.160 | 1.000 |
| application | function-head | M1 | 933,636 | 5,343.196 | 2.506 |
| quick | dependent-body | M1 | 152,816 | 2,813.970 | 2.798 |
| proof_irrelevance | proposition-type | M1 | 125,770 | 1,515.639 | 1.000 |
| lazy_delta | argument | M1 | 305,946 | 1,253.618 | 10.180 |

Projection descent is still dominant after provenance splitting. The largest
non-M1 rows are application-argument M1 -> Matched (1,048,631 calls,
71.768 ms) and lazy-delta argument M1 -> Matched (43,595 calls, 2.890 ms).

## A4: first transitions

The READY4.2 matrix does not change the prior reconstruction. The `Iso`/`Iso`
root has Matched function heads; application argument 2 enters the first
M1 `Functor.comp` pair. Successive application arguments expose
`Functor.comp`, then `DerivedCategory.Plus`/`DerivedCategory`, and a
`Functor` structure field. Projection and application congruence continue
the pair while retaining the parent's divergence hashes. The audited source
branches are `is_def_eq_app`, `is_def_eq_proof_irrel`, `is_def_eq_binding`,
and `lazy_delta_proj_reduction` in `M1P-KERNEL.md`.

## C

No C intervention was assigned to PR1624 in step 2. The READY4.2 matrix
does not identify a different cut point, so no new C run is claimed.
