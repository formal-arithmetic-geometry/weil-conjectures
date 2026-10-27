## What changed

Completed `AlgebraicGeometry.ProEtale.StrictTower.openBetaFiniteCompatibility` in
`Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization`. The proof first checks direct-image
coefficient comparisons on sections using `cUnderlying`, `cDirect` and the prescribed
compositors. Mate pasting gives pullback composition coherence. A generic square-transport
calculation gives the pullback square; the converse mate-cube theorem gives the specified
ordinary open-extension cube. `Functor.mapDerivedCategory_exactCube` then descends that
cube to the full unbounded derived category. The ordinary derived face is identified
with `ordinaryOpenExtensionBaseChangeIso` by its defining conjugate isomorphism.

Added proof-only imports of `WeilConjectures.CategoryTheory.Adjunction.MateCube`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate`
and `Sheaf.CategoryTheory.DerivedExactCube`. All helpers are private and proved. Public
signatures, definitions, instances and public imports are unchanged. Updated the owning
node's proof, proof dependencies, proof origin and obsolete top-level approval.

Validation: `deliver3.py` compiles the final module and runs the delivery preflight checks.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.StrictTower.openBetaFiniteCompatibility`
(node `lem-cbc-tower-open-beta-normalization`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the item: 0. Split off: 0.
No other module is changed.

## No longer needed

Removed the planned dependency `lem-sf-open-tensor-normalization` from the owning node's
proof, `proof_deps` and top-level `tool_uses`. The proof compares the actual ordinary
base-change mate directly and does not need `Sheaf.SixFunctors.OpenTensorNormalization`.
No existing Lean imports were removed and no module is withdrawn; the normalization
module and its other consumers remain in the library.

## Where the brief, the DAG or earlier work was wrong

The final DAG step proposed an abstract existential finite-normalization interface.
The recorded section-preserving presentation comparisons and ordinary base-change mate
already determine the required map, giving the direct argument above. No statement or
definition repair was needed. The unit's route is retained: section normalization,
open-unit adjunction mates, and exact descent before evaluation.

The concrete realization functors are expensive to unfold during component-level
cancellation. The proof keeps its composition square as a natural-transformation
square and proves cancellation/component calculations generically before specializing.
It adds no transparency relaxation or resource-limit override. Identity arrows, empty
schemes and the zero ring require no extra hypotheses: all calculations use naturality,
functoriality and adjunction laws.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
