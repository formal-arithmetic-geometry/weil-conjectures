## What changed

Completed both remaining theorem proofs in `Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison`.
`derivedComparisonUnits_natural` follows from an explicitly verified slice adjunction cocycle,
exact-derived-functor coherence, conjugation, and naturality of sheafification.
`proEtaleDerivedUnits_bijective` follows by refining local sheafification witnesses to split finite
covers and gluing sections using finite-product bijections. Isomorphisms are glued by gluing their
hom and inverse and checking the inverse equations by injectivity.

Added the fully proved module `Sheaf.AlgebraicGeometry.ProEtaleDerivedHomFiniteProducts`.
It constructs the exact direct-sum left adjoint to slice restriction, proves preservation of
K-injectives, and glues complex maps and homotopies via Mathlib's internal Hom sheaf.
The derived-category localization bijection into K-injectives gives the asserted derived Hom
bijection. Empty families are included throughout. There are no new assumptions on the item.

Added proof-only imports of `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`,
`Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`, and the new finite-product module.
The existing public signatures, definitions, and public imports are unchanged. Both modules compile
cleanly through `lcompile.py --all` (36.6 and 9.3 seconds). Updated both DAG proofs to the actual route.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.derivedComparisonUnits_natural`.
- `AlgebraicGeometry.Scheme.proEtaleDerivedUnits_bijective`.

Also proved the new theorem `AlgebraicGeometry.Scheme.proEtaleDerivedHom_finiteProducts`
(node `lem-weil-pbc-derived-hom-finite-products`). Holes added: zero. Holes left in either
delivered module: zero. This is a proof completion, not an unfinished decomposition.
The earlier attempt's report had not been updated after these proofs were written.

## No longer needed

No original imports, nodes, or modules were removed. The item node previously had no proof
steps or proof dependencies. The argument does not need a constructed equivalence between the
whole derived category on a disjoint union and a product of derived categories: internal Hom,
K-injectives, and gluing maps and homotopies suffice. No module for such an equivalence is imported.
Every added proof import supplies a used construction or theorem.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly listed `derivedComparisonUnits_natural` and
`proEtaleDerivedHom_finiteProducts` as unfinished. Both have complete Lean proofs.
The retained helper failed at one rewrite in `conjugateComparison` because the preceding
simplification had combined two functor maps; expanding `Functor.map_comp` before rewriting
fixes it. The new node's earlier proof described a derived product-category equivalence;
the implemented proof instead uses the exact slice extension adjunction and K-injectives.
Corrected its blueprint tag to match the node id and its Lean statement record to the verbatim
signature. No existing mathematical statement or public definition changed.

## New nodes

`lem-weil-pbc-derived-hom-finite-products` records the fully proved finite-product bijection
for actual local derived Hom sets, under the section-product hypothesis for set sheaves.
Its source is the finite disjoint union clause of Stacks Tag 0F63; its proof uses Mathlib's
`sheafHom` and the existing K-injective derived-category infrastructure. The node records
actual LeanFinder, Loogle, and grep searches from the retained search log; no exact theorem
was found. The blueprint ancestor search identifies `thm-weil-pbc-amplification-proper`.
There are no change records: all existing signatures and definitions are unchanged.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
