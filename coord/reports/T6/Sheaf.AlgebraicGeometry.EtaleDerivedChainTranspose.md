## What changed

Proved all four clauses of `AlgebraicGeometry.Etale.etaleDerivedChainTranspose`.
The canonical derived counit factorization already exists in Mathlib, so no
new K-injective resolution construction is needed. Two proved private helpers
carry out the counit comparison and the adjunction/naturality calculation in
arbitrary abelian categories, then specialize to the existing étale adjunction.
The public theorem's signature is unchanged. Updated its DAG proof and docstring
to this route. The public-import cleanup is recorded in
`coord/changes/t6-etale-derived-chain-transpose-imports.md`; there are no Lean
consumers to adapt. Retained explicit private imports of the termwise-adjunction API
and Mathlib's absolute-derived adjunction API. Single-file compilation verifies the full proof. An explicit `#print axioms`
check returned exactly `propext`, `Classical.choice`, and `Quot.sound`.
The final proof makes the canonical derived-adjunction equality explicit to avoid
repeated reduction during specialization. Development profiler and axiom-print
commands have been removed; delivery repeats compilation and the axiom probe.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.Etale.etaleDerivedChainTranspose`
(node `lem-sp-etale-derived-chain-transpose`). Added zero holes; split off zero
statements. No `sorry` remains in the delivered Lean module. Both private helpers
are fully proved.

## No longer needed

The old resolution-by-resolution reconstruction of an adjunction is unnecessary:
the specific adjunction in the statement is already constructed by the library's
`Adjunction.mapDerivedCategoryRightDerivedAdjunction`, which uses Mathlib's
`Adjunction.derived`. Its counit factorization gives the required normalization.

Removed unused imports:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Adjunction.Basic`

No longer direct proof dependencies of this node:
`prop-weil-pbc-inverse-image-modules-exact`, `def-weil-size-convention`,
`prop-pur-kinjective-resolutions-exist`, `def-weil-abstract-derived-category`,
`lem-weil-pbc-kinjective-total-derived`, `lem-pur-homotopy-category-triangulated`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`,
`lem-sf-kinjective-derived-map-computation`, `lem-weil-pbc-kinjective-hom-derived`,
and `lem-weil-pbc-localization-universal-property`.
These results remain in the library and some support the existing derived-functor
construction indirectly. The inverse-image and total-derived nodes remain statement
dependencies, unchanged. No module is withdrawn. Removed obsolete `tool_uses`
entries for these dependencies, retaining the termwise-adjunction entry.

## Where the brief, the DAG or earlier work was wrong

The old DAG plan reconstructs a canonical adjunction even though the theorem
already names the library's canonical absolute-derived adjunction. Mathlib's
`Adjunction.derivedε_fac_app` proves its counit square directly. The existing
Mathlib leaf `lem-sc-derived-adjunction-from-underived` records exactly that
construction and square, so this delivery reuses it and creates no node.
The unit record `sk-thm-sf-compatibility` has no realized step assigned to this
node; its statement and route are untouched.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
