## What changed

Proved both declarations in `lean/Sheaf/CategoryTheory/FixedPairDerivedForgetComparison.lean`
without changing their signatures, public imports, or existing definitions.

`CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_forget_properties` reuses the proved
source-library Grothendieck structure, exact free functor, free/forgetful adjunction,
and K-injective preservation. Injective preservation follows from Mathlib's adjunction
lemma. Derived conservativity follows by transporting cohomology through the exact
forgetful functor and applying `DerivedCategory.isIso_iff`.

`CategoryTheory.Endofunctor.IsoAlgebra.exists_fixedPairDerivedForgetComparison` applies
`KInjectiveExactSquare.existsUnique_normalized`. The new proved private helper
`homotopy_unit_ext` extends equality of natural transformations from K-injectives to all
homotopy objects by naturality along an arbitrary quasi-isomorphic resolution and
cancellation of its invertible derived image. An explicit calculation with the
localization factors gives the displayed unit equation. Reversing that calculation
reduces uniqueness to the existing comparison theorem.

Added the private proof import `Sheaf.CategoryTheory.KInjectiveExactSquareComparison`.
Updated the item's existing DAG node proof, proof dependencies, proof origin, and
removed obsolete tool approvals to match the implemented route. No new public
statement, definition, instance, or node is introduced. The unit record has no realized
statement or proof step at this node; no unit or chapter route was altered.

Validation: the final single-file compile through `lcompile.py` succeeded in 10.4 seconds
without errors or warnings. The module has zero `sorry` occurrences and all lines are at
most 100 characters. Independent derived-category universes remain unchanged.

## Proved and sorry left

Closed 2 existing holes:

- `CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_forget_properties`
  (node `lem-sf-fixed-pair-derived-forget-comparison`).
- `CategoryTheory.Endofunctor.IsoAlgebra.exists_fixedPairDerivedForgetComparison`
  (the same node).

Added 0 holes. Remaining holes in the item: none. Split off: none.
The new private helper `homotopy_unit_ext` is proved completely.
The existing arbitrary-resolution derived-functor interface remains an imported dependency;
its existing proofs and holes are unchanged.

## No longer needed

Removed these private proof imports:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp`:
  the cohomology argument for conservativity is written directly, preserving independent
  derived-category universes. Its specialized derived comparison is unnecessary.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  the comparison already quantifies over the resolution witnesses it uses.
- `Mathlib.CategoryTheory.Adjunction.Limits`: available through existing public imports;
  the additional private import is redundant.

The following five planned statement modules and their nodes are unnecessary for this
proof, because the source library already proves the needed structural facts and the
normalized exact-square theorem directly supplies the comparison:

- `Sheaf.CategoryTheory.FixedPairCreatedAbelianStructure` /
  `lem-sf-fixed-pair-created-abelian-structure`.
- `Sheaf.CategoryTheory.FixedPairFreeIntegerAdjunction` /
  `lem-sf-fixed-pair-free-integer-adjunction`.
- `Sheaf.CategoryTheory.CreatedGrothendieckExactIntegerSum` /
  `lem-sf-created-grothendieck-exact-integer-sum`.
- `Sheaf.CategoryTheory.ExactAdjointForgetDerivedDetection` /
  `lem-sf-exact-adjoint-forget-derived-detection`.
- `Sheaf.CategoryTheory.FixedPairCommonDerivedResolution` /
  `lem-sf-fixed-pair-common-derived-resolution`.

Also removed the planned dependency `lem-weil-pbc-kinjective-functorial-existence`:
`hF` and `hC` are inputs, so their existence is not required in this theorem's proof.
The inherited tool approvals for `lem-weil-pbc-kinjective-total-derived` and
`lem-weil-pbc-kinjective-hom-derived` are unnecessary as direct tools here; their use is
encapsulated in the existing normalized comparison and derived-functor interface.
The top-level approvals for `def-sp-abelian`, `def-sp-grothendieck-abelian`, and
`def-weil-abstract-derived-category` are also removed as direct proof tools; they remain
statement dependencies through the existing statements and imports.
No module is withdrawn or deleted; other consumers may still need any of these modules.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned structural split duplicated results already
proved in the source library, and the common-model statement is unnecessary for the
final normalization calculation. The upstream convenience conservativity lemma shares
one derived-category universe across two categories, whereas this item's signature
permits independent universes. Its actual cohomology proof works without that restriction
and is reused directly in the item. No upstream signature or body was changed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
