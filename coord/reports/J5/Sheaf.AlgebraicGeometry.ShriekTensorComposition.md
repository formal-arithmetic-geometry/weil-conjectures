## What changed

Proved `AlgebraicGeometry.Etale.compactSupportProjectionMap_comparison` in
`Sheaf.AlgebraicGeometry.ShriekTensorComposition`. The proof applies the existing
`projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso`, then
uses naturality of the signed tensor symmetry and of the compactification comparison.
The initial and final tensor swaps and the exact-pullback comparison are exactly those
of the original definition. Added one proof-only import:
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`.
Updated the existing node's proof to record this route. All existing signatures,
definitions, visibility, and docstrings are unchanged.

Validation: the retained two-module attempt compiled; the simplified one-module proof
also compiled through lcompile.py in 7.4 seconds.

## Proved and sorry left

Closed one of the item's two original holes:
`AlgebraicGeometry.Etale.compactSupportProjectionMap_comparison`
(node `lem-amb-shriek-tensor-composition`).

Remaining original hole:
`AlgebraicGeometry.Etale.compactSupportProjectionMap_comp`
(node `lem-amb-shriek-tensor-composition`). Its original fourteen-step proof plan and
all recorded dependencies are retained. The missing work is compatibility of the
specified proper/open tower compositor with tensor projection, followed by inversion
of the resulting square. The existential composition-coherence statement upstream
does not identify its witness with this specified tower compositor.

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 1.
This is a proof of the comparison clause, with no decomposition or new sorry theorem.

## No longer needed

The retained attempt's undelivered `Sheaf.AlgebraicGeometry.ProjectionCartesianRefinement`
module and `lem-amb-projection-cartesian-refinement` node are unnecessary: the source
library already proves the whole right-factor comparison square, including its
common-refinement cancellation. Their files and change record have been removed from
the sandbox delivery. Neither exists in the current shared repository, so this is
removal of an undelivered duplicate, not withdrawal of a landed module.

No original imports were removed. The original dependencies remain necessary to the
still-open composition proof. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly named the helper as the closed original obligation.
The original item has two holes; the theorem closed by this delivery is
`compactSupportProjectionMap_comparison`, and the composition theorem remains open.
The proposed helper duplicated an existing unbounded refinement theorem, and even its
common-refinement assembly is already available in LowerShriekProjectionExchange.
The successful shortcut is below the unit level and preserves the specified maps.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
