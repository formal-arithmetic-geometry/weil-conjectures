## What changed

Completed `clopen_unbounded_derived_localization` in `Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization` with its original `LocalizationStatement` byte-for-byte unchanged. The proof assembles complexes and homotopies coordinatewise, descends the specified unit and counit through both localizations with their exact normalization and triangles, proves the product shift and triangle comparisons, constructs the two finite bilimit bicones, and handles empty components, zero coefficient sheaves, and the empty partition.

Added fully proved private helpers in the same module. Reused Mathlib localization/adjunction APIs and the adopted source library's proved exact-derived-functor composition, natural-isomorphism, cohomology and zero-object API through private proof imports. No adopted source-library file changed.

Packaged the specified sectionwise module equivalence as `FixedEquivalence` and `recordedEquivalence`, avoiding repeated expansion of nested choice witnesses. Constructed insertion explicitly by coordinate zero insertion followed by the same gluing functor, with its additivity and exactness proved for that construction. Changed `restriction` from an abbreviation to a definition with the identical type and body. These definition/API repairs are recorded in `coord/changes/Q8-clopen-localization-restriction.md` and `coord/changes/Q8-clopen-localization-specified-data.md`. The existing node records the actual proof route and all added public support declarations.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.clopen_unbounded_derived_localization` (node `lem-pur-clopen-unbounded-derived-localization`). Holes closed: 1; holes added: 0; holes remaining in the delivered module: 0; split-off statements: 0. The existing `restriction_exact`, `insertion_additive` and `insertion_exact` remain proved.

Verification: the full assigned module compiles without warnings in 56.3 seconds under the unchanged 60-second limit. A rebuilt `#print axioms` audit reports exactly `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`. The four current original downstream modules compile unchanged against the revised module: `ProEtaleClopenDerivedScalarCompositor` (P8), `ProEtaleClopenKFlatMonoidalDescent` (P9), `ClopenCompletedOperationTowers` (Q5), and `ClopenCompositeCounitNormalization` (unclaimed). No forced adaptation is necessary. Temporary probes and consumer copies are excluded from the delivery.

## No longer needed

Removed the proof import `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory` and the node proof dependency `lem-galois-equivalence-preserves-limits`. The bilimit proof uses explicit coordinate projection/inclusion maps, their total-identity equation, additive whiskering, and transport along the derived insertion comparisons; it does not need an equivalence-preserves-limits argument in functor categories. Removed the unused private helper `faithful_of_unit`, using the packaged equivalence's faithful-functor API instead.

The inverse derived functor's preservation of distinguished triangles comes from the triangulated-adjunction theorem, so a separate signed mapping-cone matrix computation is unnecessary. The adopted proved cohomology comparison also avoids repeating that localization descent. All other declared mathematical dependencies are used. No Lean module is withdrawn, and no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound. Its cone computation and preservation-of-biproducts route were longer than the available generic APIs and direct total-identity criterion. The nested `Classical.choose` definitions caused repeated expensive elaboration in the complete proof; fixing the forward functor in the packaged data and constructing insertion explicitly makes the normalization usable within the existing compile limit. The chosen gluing data still come from the full proved section-and-morphism formula theorem, and the localization statement is unchanged.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
