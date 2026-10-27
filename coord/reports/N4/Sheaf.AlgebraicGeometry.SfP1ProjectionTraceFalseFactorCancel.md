## What changed

Proved `AlgebraicGeometry.Etale.SfP1Transport.falseProjectionChartFactor_cancel`
in `Sheaf.AlgebraicGeometry.SfP1ProjectionTraceFalseFactorCancel` without changing
its statement, the displayed inverse construction, or either public import.
Install the existing `isIso_ordinaryFiniteP1Exchange` result, unfold the two
chart factors, reassociate, cancel the functor images of the shifted-line
isomorphism and its inverse with `Iso.map_hom_inv_id_assoc`, and cancel the
exchange and its inverse with `IsIso.hom_inv_id`.

Updated the item's node proof to record these two elementary cancellation steps
and corrected its Lean module attachment to match its existing file path.
The source is the chart-factor inverse/direct-image cancellation in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-geo-p1-adjunction/thm-amb-p1-adjunction.proof.md`.
The unit statement and its realized proof steps are preserved.

Remote single-file compilation succeeded with no warnings in 5.8 seconds.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Etale.SfP1Transport.falseProjectionChartFactor_cancel`
(node `lem-sf-p1-projection-trace-transport-false-factor-cancel`).

No holes remain in the item. Added zero holes and split off zero statements.

## No longer needed

None. Both original imports remain necessary for the existing public
construction and theorem. The sole declared proof dependency,
`lem-asd-ordinary-finite-p1-exchange-iso`, is used. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item's node attached its theorem to
`Sheaf.AlgebraicGeometry.SfP1ProjectionTraceFalseMate`, although its `lean.file`
already named `SfP1ProjectionTraceFalseFactorCancel.lean`. Corrected only the
module component of that attachment. The statement and planned cancellation
argument were correct and admit a complete proof without further decomposition.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
