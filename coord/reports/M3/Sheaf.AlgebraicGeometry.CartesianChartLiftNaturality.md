## What changed

Retire `Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality`, a current retirement
item, by listing its path in `deleted.txt`. Its public theorem
`AlgebraicGeometry.Etale.cartesianChartCohomologyLift_naturality` is already proved
in `WeilConjectures.AlgebraicGeometry.CartesianChartLiftNaturality` with exactly
the same signature (token comparison ignoring whitespace). The existing upstream
`CartesianRawClassChartNaturality` caller already imports and applies that theorem.
There are no current or quarantined consumers to adapt.

Validation through `lcompile.py`: an import/check of the published upstream theorem
compiles in 2.0 seconds and `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The unchanged actual caller
`WeilConjectures.AlgebraicGeometry.CartesianRawClassChartNaturality` compiles in
9.9 seconds. The unchanged historical failed consumer
`WeilConjectures.AlgebraicGeometry.RawDerivedClassAffineDescent` compiles in
33.7 seconds. A separate attempt to recompile the entire unchanged upstream
naturality source hit the 60-second limit; no upstream source is changed or
submitted, and the successful checks above use the existing published upstream
artifact. Verification snapshots live only under the sandbox scratchpad and are
not part of the delivery.

Change record: `coord/changes/M3-cartesian-chart-lift-naturality-retirement.md`.

## Proved and sorry left

Zero current holes: the withdrawn module has zero `sorry`, and this delivery
closes zero holes, adds zero holes, and splits off zero statements. The existing
upstream theorem retains its complete proof unchanged. This is duplicate retirement,
not a claimed new proof. No other Lean source is delivered.

## No longer needed

Withdrawn module: `Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality`.
Its following imports disappear with the duplicate (their upstream declarations
remain available where used):

- `WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback`.
- `WeilConjectures.AlgebraicGeometry.CartesianChartExchangeComparison`.
- `WeilConjectures.AlgebraicGeometry.AbelianRawPullbackComposition`.
- `WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift`.
- `WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality`.
- `WeilConjectures.AlgebraicGeometry.CartesianChartExchangeMapNaturality`.
- `WeilConjectures.AlgebraicGeometry.CartesianChartExchangeConclusion`.
- `WeilConjectures.AlgebraicGeometry.CartesianChartExchangeFinal`.
- `WeilConjectures.AlgebraicGeometry.CartesianChartExchangeObjects`.
- `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`.
- `Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence`.
- `Sheaf.AlgebraicGeometry.CartesianChartDiagramMap`.
- `Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality`.

The alternative proof's helpers `Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence`,
`Sheaf.AlgebraicGeometry.CartesianChartDiagramMap`, and
`Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality` are not needed by the
upstream replacement. They are not withdrawn in this packet. No DAG node or unit
record refers to the item module or its blueprint tag, so there is no dependency
or attachment to remove. `tools/downstream.py` reports zero downstream modules;
search of all current Lean and quarantined source confirms zero imports.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief and historical M3 return predate the present retirement
assignment. The current queue and retire-items table list this item as `retire`.
The old return's chart-pullback-core definition change is absent from the current
source; restoring it would reintroduce an unnecessary definition/interface change.
The present upstream chart-class pullback definition is preserved, including all
its construction data. The existing raw affine-descent proof and actual theorem
consumer are validated unchanged.

No node attached to this module was found in the current DAG; none is invented
for an already proved duplicate. LeanFinder returned generic scheme-pullback
identities; Loogle and Mathlib grep returned no chart-lift theorem. Local source
search found the exact upstream theorem and its existing caller.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
