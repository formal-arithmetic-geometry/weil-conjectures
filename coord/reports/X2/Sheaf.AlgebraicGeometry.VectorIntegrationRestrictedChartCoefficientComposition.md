## What changed

Proved `AlgebraicGeometry.Etale.vectorIntegration_restricted_chart_coefficient_composition`
in its original module, with its statement unchanged. Added proof imports of
`Sheaf.Paper.OrderedTateExactOpenComposition` and
`WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube`.
Private proved helpers convert the existing exact ordinary Tate transport equation
back to derived pullback coordinates. The main proof uses square pasting, naturality,
and cancellation. Generic private isomorphism lemmas avoid expensive dependent
rewriting through the concrete derived categories. Only local elaboration attributes
are used; no shared definition or interface changes.

Updated the item's DAG proof and proof dependencies to describe this reuse.
`lem-pur-ordered-tate-exact-open-composition` is used as a generic coefficient
composition tool: its proved nested-open transport equation is exactly the base
coefficient calculation needed here. It does not replace any step of the unit route.
The unit record `sk-prop-an` has no realized node assigned to this item.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.vectorIntegration_restricted_chart_coefficient_composition`
(node `lem-amb-vector-integration-restricted-chart-coefficient-composition`).
No holes remain in the item. No holes or split-off modules were added.
The full module compiled through `lcompile.py` in 17.9 seconds with profiling enabled;
all diagnostic options were removed for delivery.

## No longer needed

No original import was removed and no module was withdrawn. The original proof
need for inverse-image coherence and the chart constructions remains.
The affine tower base-change recursion
`lem-amb-vector-integration-restricted-chart-coefficient-core` is not used by this
proof: the input equation has already replaced that base-change factor by coefficient
descent. Its separate consumers still need it. No global pruning is claimed.
The ordered Tate composition argument is reused from the proved module instead of
repeated or split off again here.

## Where the brief, the DAG or earlier work was wrong

The original single proof step understated the coefficient calculation: inverse-image
associativity alone does not identify the two ordered Tate transport maps. The now-proved
`orderedTateExactOpenComposition` supplies that missing input. Its exact ordinary
coordinates require conjugating by the existing exact-to-left-derived comparisons.
No statement repair or change to the blueprint route was needed. The formulas work
unchanged in rank zero, for empty opens, and for the zero coefficient ring.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
