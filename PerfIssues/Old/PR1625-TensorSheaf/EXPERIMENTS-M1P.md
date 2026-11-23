# PR1625: M1 propagation (READY4.2)

## Validation

The fresh original `OriginalNestedApp.lean` probe ran with READY4.2 Lean
4.35.0 at root 65966. The analyzed root and the separate counters run each
have 11,757,788 calls, equal to the accepted READY3.2 count. M1 is
8,111,028 calls (68.984% of calls) and 99.546% of comparison-exclusive
time, within 0.5 percentage points of READY4.1 (99.437%).

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.693 | 0.001% |
| M1 | 8,111,028 | 91,299.219 | 99.546% |
| M2 | 4,686 | 58.740 | 0.064% |
| Matched | 3,642,041 | 355.963 | 0.388% |
| Unclassified | 32 | 0.811 | 0.001% |

Analyzer: READY4.2 `mprwe_analyze.py`, kernel dataset commit
`0311a15b5f4`. Aggregate coverage is 11,757,788/11,757,788 calls; raw
capture is 1,703 entered and 1,613 exited calls (0.0145%). The aggregate
matrix reconciles to 11,757,787 child edges plus 0.693 ms root-direct time.
No depth was clamped.

## A2: topology

M1 depth mean/median/p90/p99/max is 100.093/101/112/119/125. The narrowest
bands containing 50% and 90% of M1 exclusive time are 95-107 and 85-115.
M1-parent fan-out mean/median/p90/max is 1.448/1/3/28. M1 -> M1,
M1 -> Matched, and M1 -> M2 edge counts are 8,104,569, 3,638,816, and
3,907. The analyzer verdict is **deep**: median depth is at least 75,
mean fan-out is at most 1.5, and the 90%-time band is 31 levels wide.

## A3: M1-parent transition matrix

The first seven rows cover 99.3% of M1 exclusive time. Parent outcomes are
separate fields and are not used as initiating branches.

| Initiating branch | Child kind | Child label | Calls | Child exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| projection | projection | M1 | 1,697,606 | 39,690.038 | 1.000 |
| application | argument | M1 | 3,440,720 | 27,459.675 | 3.972 |
| application | function-head | M1 | 1,369,438 | 8,749.126 | 2.502 |
| second_whnf | whnf-iota-exposure | M1 | 562,739 | 5,934.297 | 1.000 |
| lazy_delta | argument | M1 | 547,603 | 3,702.034 | 5.124 |
| quick | dependent-body | M1 | 247,558 | 3,279.294 | 1.342 |
| proof_irrelevance | proposition-type | M1 | 154,195 | 2,286.212 | 1.000 |

Projection descent remains the dominant M1 transition. The largest
non-M1 rows are lazy-delta argument M1 -> Matched (729,059 calls,
140.984 ms) and application-argument M1 -> Matched (1,931,669 calls,
124.814 ms).

## A4: first transitions

The provenance-keyed matrix leaves the READY4.1 reconstruction unchanged.
The Pi/Pi root enters the dependent `Eq`/`Eq` body through
`quick -> dependent-body[15]`. Application argument 0 compares
`Quiver.Hom`; the costly sibling then compares `CategoryStruct.comp`,
descends through `DFunLike.coe`, `EquivLike.coe`, `Equiv.toFun`,
`Equiv.proj`, and `equivShrink`. The repeated projection child pairs keep
the inherited divergence hashes and therefore remain M1. The audited
branches are `is_def_eq_binding`, `is_def_eq_app`, and
`lazy_delta_proj_reduction` in `M1P-KERNEL.md`.

## C: M0-preserving cut point

The nested major-premise alignment changes the outer dependent telescope
and removes M0. No replacement at the original instantiated type was
constructed, so O-cut/O-restore is invalid. C remains blocked by the
dependent domain.
