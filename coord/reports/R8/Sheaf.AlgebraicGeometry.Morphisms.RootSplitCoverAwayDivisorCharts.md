## What changed

Retired `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts`, a listed
retirement item, and redirected the `lean` record of
`lem-sbc-root-split-cover-away-divisor-charts` to the existing theorem in
`WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts`.
The source library is unchanged. There are no remaining importers of the Sheaf copy;
the former cyclic-chart consumer has already moved to the upstream theorem.

The upstream theorem omits the copy's unused `hj` hypothesis and uses nondependent
`Fin d` function notation for the same product. A scratch `example` retaining the
entire old signature compiled by applying the upstream theorem directly. The
unchanged source cyclic-chart consumer also compiled (2.6 seconds), and the old
copy compiled before retirement (2.1 seconds).

Change record: `coord/changes/retire-root-split-cover-away-divisor-charts.md`.

## Proved and sorry left

Actual initial holes in the assigned module: **0**. Holes closed: **0 of 0**.
Holes added or split off: **0**. No `sorry` remains in the delivery.

The existing upstream
`AlgebraicGeometry.Scheme.root_split_cover_away_divisor_charts` proves the required
statement. Its `#print axioms` output is exactly `propext`, `Classical.choice`,
`Quot.sound`, so the entire dependency chain of this theorem is already proved.
The compiled specialization checks that the redundant old hypothesis causes no
loss in the conclusion. This delivery counts one retired module, not a new proof.

## No longer needed

Retired module: `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts`.
The redundant declaration and all six imports disappear with its withdrawal:
`Mathlib.AlgebraicGeometry.Limits`, `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`Mathlib.RingTheory.AdjoinRoot`, `Mathlib.Algebra.Algebra.Pi`,
`WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayLocalizationPoint`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayTransportChart`.
These modules remain available through the upstream theorem where needed.

No mathematical node or proof dependency is pruned. In particular,
`lem-sbc-root-split-away-localization-point` and
`lem-sbc-root-split-away-transport-chart` are still used by the upstream proof.
The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open obligation split off many times, but
this assignment is currently a retirement item with zero holes, not an unfinished
proof. Its full chain is already proved in the adopted source library.

The retirement table's former consumer
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel` has already been
retired. Its upstream replacement imports the upstream away-divisor theorem and
already drops the `hj` argument. Therefore no consumer adaptation is needed here.
The node's previous Sheaf attachment was the remaining stale reference.

Searches: LeanFinder returned standard-etale presentation ingredients; Loogle
`AdjoinRoot, AlgebraicGeometry.Etale` returned no hits. Direct library search found
the stronger, fully proved upstream theorem and its already-adapted consumer.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
