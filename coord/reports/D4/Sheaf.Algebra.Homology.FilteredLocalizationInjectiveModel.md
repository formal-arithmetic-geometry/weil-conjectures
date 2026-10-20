## What changed

The item now proves the localization Hom bijection, the comparison equivalence, the triangulated comparison, termwise injectivity, and the comparison isomorphisms. The two long source constructions are isolated as the genuinely separate theorems `filteredInjectiveResolution` and `filteredAcyclic_injective_vanishing`, each imported by the item. The proof uses the localization fraction API and Mathlib's triangulated exactness; the previous cone-localization import is no longer needed by this proof.

## Proved and sorry left

Closed the item hole `CategoryTheory.filteredLocalization_injectiveModel` (1 of 1). One strictly smaller source result remains as a named hole: `CategoryTheory.filteredInjectiveResolution` in `lem-trf-filtered-injective-resolution`. The contraction result `CategoryTheory.filteredAcyclic_injective_vanishing` is proved in this delivery. Holes closed: 1; holes added: 1; this is a decomposition with zero net hole reduction, plus a fully proved new source lemma. There are no holes in definitions or private declarations. All three modules compile without warnings through `lcompile.py --all`; this was rechecked after resumption on 2026-10-20. The measured uncached runs were 34.3 seconds for vanishing and 32.0 seconds for the item.

## No longer needed

Removed the direct proof imports `Sheaf.CategoryTheory.DoubleComplexTotal`, `Sheaf.Algebra.Homology.FirstQuadrantAugmentation`, `Mathlib.Algebra.Homology.HomologySequence`, `Mathlib.Algebra.Homology.HomologySequenceLemmas`, `Sheaf.Algebra.Homology.FilteredComplexSubquotients`, `Sheaf.Algebra.Homology.FilteredConeLocalization`, `Sheaf.CategoryTheory.EnoughStrictFilteredInjectives`, `Sheaf.Paper.FiniteFilteredGradedExactness`, and `WeilConjectures.CategoryTheory.Abelian.Filtration` from the item; the two split modules import the strict-injectivity, exactness, and totalization declarations they need. The contraction module additionally contains a proved generic cochain induction and filtered extension lemma. The proof does not use `lem-trf-filtered-cone-localization` or its module anywhere in the new route. The other removed imports remain dependencies of the isolated resolution or contraction results, or are already public prerequisites of `FiniteFilteredLocalization`; they are not globally pruned. The tool-use approval for `lem-sc-first-quadrant-column-augmentation` remains: the resolution construction still needs it.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was changed. The resumed dry run reported missing LeanSearch records for both new nodes; actual LeanSearch queries were run and recorded, alongside the earlier LeanFinder, Loogle and grep searches. The twelve-step plan contains two separately named source results (Tags 05TW and 05TX); isolating these makes the remaining localization and comparison proof direct. The cone-localization theorem is also unnecessary for the Hom bijection: the acyclic cone argument uses Mathlib's distinguished-triangle exactness after the vanishing result.

Consumer check: the theorem signature and public imports are unchanged. Existing importers are `FilteredGlobalHomExactAdjunction`, `BoundedInjectiveFibreDescent`, `FilteredDerivedHomCalculusUniverse`, and `FilteredDerivedOperationLifts`; they require no adaptation. The new splitting import is cycle-free by `import_direction.py`. The unit realization route is preserved.

## New nodes

`lem-trf-filtered-injective-resolution` records the Tag 05TW resolution construction and its fixed-interval refinement; its Lean module is `lean/Sheaf/Algebra/Homology/FilteredInjectiveResolution.lean`.

`lem-trf-filtered-acyclic-injective-vanishing` records the Tag 05TX contraction of maps from graded-acyclic complexes; its Lean module is `lean/Sheaf/Algebra/Homology/FilteredAcyclicInjectiveVanishing.lean`, and its theorem is proved here.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
