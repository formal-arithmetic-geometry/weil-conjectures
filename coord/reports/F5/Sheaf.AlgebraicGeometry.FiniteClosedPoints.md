## What changed

Proved `AlgebraicGeometry.IsClosed.finite_of_finiteType_over_field_of_closed_points`
in `Sheaf.AlgebraicGeometry.FiniteClosedPoints`, following the existing two-step DAG plan.
Mathlib's `LocallyOfFiniteType.isLocallyNoetherian` supplies local Noetherianity of X;
`QuasiCompact.compactSpace_of_compactSpace` supplies compactness. The Noetherianity
and compactness of Spec K are inferred from the field instance. Apply the existing
proved `AlgebraicGeometry.finite_of_isClosed_of_closed_points` to E.

The signature, docstring, imports and visibility are unchanged. The existing node
`lem-kun-finite-closed-subscheme` already records exactly these dependencies and route,
so no node changes are needed. Single-file server compilation passed in 1.2 seconds.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.IsClosed.finite_of_finiteType_over_field_of_closed_points`
(node `lem-kun-finite-closed-subscheme`). No holes remain in the item; no holes added
and no statements split off. Its finiteness dependency is already proved.

## No longer needed

None. Both declared dependencies remain used:
`lem-weil-pbc-finite-type-over-noetherian` through its Mathlib match, and
`lem-sc-noetherian-closed-points-finite` through
`Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`.
No imports, nodes or modules are removed. The public imports provide the morphism
classes in the unchanged signature; the proof import provides the finiteness theorem.

## Where the brief, the DAG or earlier work was wrong

None. The plan matches the available declarations, and the unit route is preserved.
The empty closed subset and empty scheme require no exceptions: the general finiteness
lemma handles them, and this proof introduces no nonemptiness hypotheses.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
