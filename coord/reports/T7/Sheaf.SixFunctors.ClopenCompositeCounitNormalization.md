## What changed

Proved `AlgebraicGeometry.ProEtale.ClopenCompositeCounit.clopenCompositeCounitNormalization`
in `Sheaf.SixFunctors.ClopenCompositeCounitNormalization`, with all four conjuncts and
all specified maps unchanged. Four proved private helpers establish the sheaf counit
normalization, its exact-derived localization, and the identification of the comparison
with the canonical right-adjoint isomorphism. The final cancellation uses naturality,
`unit_conjugateEquiv`, and the right triangle identity.

Added the private proof import
`Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition` for the already-proved
cochain formula `mapDerivedCategoryIdIso_hom_app_Q_obj`. Updated the item's proof,
proof dependencies and proof origin to match this argument. All existing public imports,
signatures and non-theorem definitions remain unchanged. No other Lean module is edited.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.ClopenCompositeCounit.clopenCompositeCounitNormalization`
(node `lem-sf-clopen-composite-counit-normalization`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. No split-off theorem.
The private helpers `exact_counit`, `sheaf_counit`, `derived_counit`, and `comparison_eq`
are all proved.

The module compiled without warnings through `lcompile.py` in 14.1 seconds.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The proof
does not need the published finiteness assumption; its signature retains that assumption
verbatim, with the unused-section-variable linter disabled only for this theorem.

## No longer needed

Removed the private imports and corresponding unused proof dependencies:

- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`
  (`lem-pur-clopen-ringed-module-gluing`).
- `Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization`
  (`lem-pur-clopen-unbounded-derived-localization`).
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
  (`lem-pur-site-restriction-module-adjunction-exact`).

Removed these three obsolete entries from the node's top-level `tool_uses`, retaining
the original order of the remaining entry. These modules and nodes are unnecessary for
this proof because its existing canonical sheaf comparison and reverse sheaf adjunction
already supply the required clopen construction. They are not withdrawn: other proofs
may still use them. No further declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The original product-gluing route was longer than necessary for the Lean constructions
already present in the item. The source library already proves that the canonical
clopen extension-to-direct-image comparison is invertible, and proves its compatibility
with the restriction adjunction. Transporting that identity to upperStar and then
localizing gives precisely the required counit normalization. Right-adjoint uniqueness
then supplies the projector/unit identity without introducing product-category coordinates.

The final compositor equation retains the inverse pullback compositor explicitly;
`unit_conjugateEquiv` has exactly this orientation. No statement or definition repair,
forced adaptation, new node, or change to the blueprint unit route is required. The
argument uses no nonempty-scheme or nonzero-ring assumption, including when s is the
identity or either clopen piece is empty.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
