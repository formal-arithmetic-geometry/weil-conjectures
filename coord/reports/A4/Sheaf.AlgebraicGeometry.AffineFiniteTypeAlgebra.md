## What changed

Replaced the proof of `AlgebraicGeometry.affine_finiteType_algebra_of_field` in
`Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`. The statement, docstring and imports
are unchanged. `HasRingHomProperty.appTop` for `LocallyOfFiniteType` applies the planned
affine-pair criterion to the top opens. Composing this finite-type ring homomorphism
with the surjective inverse of `Scheme.ΓSpecIso` proves finite type for exactly the
algebra structure in the conclusion. This is the existing DAG argument, so no node
update is necessary.

The assigned module compiled without warnings through `lcompile.py` (1.8 seconds).
The delivery dry run also checks the axioms of every declaration.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.affine_finiteType_algebra_of_field`
(node `lem-pc-affine-finite-type-algebra`). No holes remain and no holes were added.
This is a proof from Mathlib, not a decomposition into new obligations.

## No longer needed

None. Both original public imports are needed by the unchanged statement.
The proof retains the planned dependencies `def-weil-finite-type-morphism` and
`lem-weil-pbc-lft-affine-pairs`, using their Mathlib implementations. No project
proof modules, extra imports or new nodes are needed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The source's existing argument in
`WeilConjectures.AlgebraicGeometry.AffineSpace.Line` confirms the same short
Mathlib composition proof. The quasi-compactness hypothesis is unnecessary for
the argument but is retained exactly as assigned. The proof also accommodates
the empty affine scheme, whose global-section ring is the zero ring; no
nontriviality of that ring is used.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
