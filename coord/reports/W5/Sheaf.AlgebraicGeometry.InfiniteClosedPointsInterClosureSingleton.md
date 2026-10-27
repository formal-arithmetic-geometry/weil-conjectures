## What changed

Proved `AlgebraicGeometry.infinite_closedPoints_inter_closure_singleton` in
`Sheaf.AlgebraicGeometry.InfiniteClosedPointsInterClosureSingleton` directly from Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` and `closure_inter_closedPoints`.
A finite set of ambient closed points is closed, so Jacobson density would force the
nonclosed point itself to be closed. The statement, universes, and public imports are unchanged.
Updated the theorem's proof description and its DAG proof to match this argument.
The module compiled through lcompile.py; delivery preflight also checks its axioms.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.infinite_closedPoints_inter_closure_singleton`
(node `lem-sc-finite-type-nonclosed-closure-closed-points`).
No holes remain in the module. No holes added; no statements split off.
The proof uses only Mathlib, without any theorem depending on `sorry`.

## No longer needed

Removed the private proof import
`Sheaf.AlgebraicGeometry.InfiniteClosedPointsInterOfTopologicalKrullDimPos`.
The proof no longer needs its declaration
`AlgebraicGeometry.infinite_closedPoints_inter_of_topologicalKrullDim_pos`
or node `lem-sc-positive-dimensional-locally-algebraic-closed-points`.
Consequently none of that node's dimension, reduced-closed-subscheme, affine-closed-point,
or infinite-maximal-ideal argument is needed by this theorem. Those modules are not
withdrawn: other parents may still need them. The replacement dependency is the existing
Mathlib leaf `lem-sc-lft-over-field-jacobson-space`, in the same unit.
No public import was removed.

## Where the brief, the DAG or earlier work was wrong

The original plan was valid but unnecessarily used positive Krull dimension and an affine
maximal-ideal infinitude theorem. Jacobson density alone proves the result by contradiction.
The algebraic-closedness hypothesis is unnecessary for this proof; it is preserved verbatim.
The unit's own statement and proof steps are unchanged; this is a shorter proof below the
unit level. Sources read: Stacks `varieties.tex`, `lemma-locally-finite-type-Jacobson`
(Tag 0478), and `topology.tex`, `definition-space-jacobson`.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
