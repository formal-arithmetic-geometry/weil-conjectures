## What changed

Proved `CochainComplex.exists_functorial_boundedAbove_class_resolution` in
`Sheaf.Algebra.Homology.FunctorialBoundedAboveClassResolution`, without changing its
statement, universes, visibility, or existing public imports.

Added proof-only imports of `Sheaf.Algebra.Homology.LeftResolutionReducedClass` and
`Sheaf.Algebra.Homology.LeftResolutionBoundedMinus`. The proof follows the two steps
of `lem-sfb-functorial-bounded-above-class-resolution` exactly. To supply the first
step's retract hypothesis, a split mono `i : X ⟶ Y` gives
`Y ≅ X ⊞ cokernel i` by Mathlib's splitting/biproduct API; iso-closure and the given
summand closure imply `F X`. The reduced-class theorem then supplies the auxiliary
category, inclusion, and cover. Uniqueness of zero-morphism structures identifies
its explicitly supplied structure with the preadditive one, allowing application
of the bounded-minus theorem. Iso-closure transfers membership in `F` to each
resolution term; quasi-isomorphisms and all upper bounds are retained directly.

Single-file verification through `lcompile.py`: exit 0, 2.3 seconds, no warnings.
Both new imports are used. No definition, statement, or other module was changed;
the existing node proof and its proof dependencies already describe this route.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.exists_functorial_boundedAbove_class_resolution`
(node `lem-sfb-functorial-bounded-above-class-resolution`).

Item holes: 1 before, 0 after. Added holes: 0. Split-offs: 0.
No `sorry` remains in the delivered module.

The proof uses the existing declarations
`CategoryTheory.Abelian.leftResolution_reduced_class`
(node `lem-sfb-left-resolution-reduced-class`) and
`CochainComplex.exists_functorial_boundedAbove_left_resolution`
(node `lem-sfb-left-resolution-bounded-minus`), whose proofs are still `sorry` in
the shared source. These are existing dependency obligations, not new holes or
claims of a proof free of transitive sorries.

## No longer needed

None. No imports, nodes, or modules were removed. Both declared resolution
steps are used; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The reduced-class Lean statement expresses direct
summand closure as closure under retracts, while the item's hypothesis uses binary
biproduct summands. The proof explicitly bridges these equivalent conditions in
an abelian category. Its separate zero-morphism structure also needs transport
by the subsingleton instance before invoking the bounded-minus statement.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
