## What changed

Proved `AlgebraicGeometry.geometricallyIrreducible_spec_of_field_subextension` in
`Sheaf.AlgebraicGeometry.GeometricIrreducibilitySubextension` without changing its
signature or imports. Apply the existing
`AlgebraicGeometry.geometricallyIrreducible_spec_of_injective` to
`IsScalarTower.toAlgHom k L K`; injectivity is `(algebraMap L K).injective`.
This implements the two existing DAG steps exactly (Stacks Project, Tag 037N(1)).
The field tower supplies compatibility with k, and fields supply injectivity.

The server single-file compile passed in 1.8 seconds with no diagnostics.
Mathlib semantic, Loogle and source searches found no shorter geometric
irreducibility result; Loogle confirmed the existing `RingHom.injective` lemma.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.geometricallyIrreducible_spec_of_field_subextension`
(node `lem-zl-geometric-irreducibility-subextension`).
No holes remain in the item; no holes or declarations were added elsewhere.
The proof uses the existing stated general subalgebra theorem
`AlgebraicGeometry.geometricallyIrreducible_spec_of_injective`, whose proof is
still sorry in its own module. That pre-existing dependency is unchanged.
This is a proof from the assigned declarations, with no decomposition.

## No longer needed

None. No imports were removed; the sole existing import supplies the general
subalgebra theorem and the statement's vocabulary. Both existing proof
dependencies (`def-pc-field-extension` and
`lem-zl-geometric-irreducibility-subalgebra-colimit`) are used. No nodes or
modules are pruned and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The existing plan and declaration fit directly. The cases L = k and
L = K require no separate treatment, and no separability or reducedness
assumption was added. The proof is independent of those properties.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
