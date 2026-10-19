## What changed

Proved the module composition and identity equations, derived composition and identity equations, and
coefficient compatibility theorem in `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`.
Added the proof-only import `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`
for its derived identity and composition coherence lemmas. All existing signatures are unchanged.

## Proved and sorry left

Closed 5 of 12 original theorem holes; added 0 holes; 7 theorem holes remain.
Proved `CategoryTheory.localizationInverseImage_comp` by unit-preserving uniqueness,
`CategoryTheory.localizationInverseImage_id` by the same argument for the identity,
`CategoryTheory.localizationComparisonDerived_comp` by derived whiskering and associativity,
`CategoryTheory.localizationComparisonDerived_id` by derived identity coherence, and
`CategoryTheory.localizationInverseImage_coefficient` by specialization of composition.

Sorries remain in `CategoryTheory.existsUnique_scalarLocalizationUnit`,
`CategoryTheory.localization_inverseImage_exact`,
`CategoryTheory.existsUnique_localizationInverseImage`,
`CategoryTheory.existsUnique_localizationInverseImageRing`,
`CategoryTheory.localizationInverseImage_fraction`,
`CategoryTheory.localizationComparisonDerived_unit`, and
`CategoryTheory.localization_restrictScalars_fullyFaithful`.
All belong to node `lem-weil-pbc-localization-inverse-image-coherence` and retain their
sources and complete natural-language proof plans. No new split-off theorem was introduced.
`localizationUnitDerived` is an unchanged definition with no hole.
The module compiled successfully with `lcompile.py` against the current baseline.

## No longer needed

No imports, modules or DAG dependencies were removed. No new node was needed.

## Where the brief, the DAG or earlier work was wrong

The retained report understated the completed work as only the coefficient theorem.
The retained derived composition attempt contained an unfinished rewrite. The missing
comparison factors are now inserted using derived associativity and cancelled explicitly,
closing the theorem without adding a hole.
No statement, definition or unit route was changed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
