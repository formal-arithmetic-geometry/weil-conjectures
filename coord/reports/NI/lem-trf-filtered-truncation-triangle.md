## Worker report

The module `Sheaf.Algebra.Homology/FilteredTruncationData` introduces the helper
structure `CochainComplex.FiniteFiltered.FilteredTruncationData`; the module
`Sheaf.Algebra.Homology.FilteredTruncationTriangle` states
`CochainComplex.FiniteFiltered.filteredTruncationTriangle` as its nonemptiness theorem.
The structure is grounded in the existing finite filtered bounded-below localization
(`CochainComplex.FiniteFiltered.Derived false`) and its cone-normalized triangulation.
It records the exact forgetful and graded functors, exact subcomplex and quotient
truncations, their canonical maps and representative comparisons, the distinguished
triangle, support conditions, uniqueness, both Hom-set bijections and their naturality,
and the pure-grade placement equivalence. The only proof is the required `sorry` on
`filteredTruncationTriangle`; the structure has no postponed data.

The module imports `Sheaf.Algebra.Homology.FilteredDerivedHomCalculus` and
`Sheaf.Algebra.Homology.FiniteFilteredLocalization`, which supply the filtered complex,
localization, cone, shift, truncation representative, and derived-category declarations.
`CategoryTheory.Abelian` is the Mathlib realization of `def-sp-abelian`.
`CategoryTheory.DecreasingFiltration` is the recorded upstream declaration for
`def-sp-filtration`, and `CategoryTheory.DecreasingFiltration.complexCycles` (with its
sibling declarations in `Sheaf.Algebra.Homology.FilteredComplexSubquotients`) is the
recorded declaration for `def-sp-filtered-complex-subquotients`.
`DerivedCategory`/`DerivedCategory.Plus` are the Mathlib declarations for
`def-weil-abstract-derived-category`; `CategoryTheory.Pretriangulated` and
`IsTriangulated` supply `def-weil-triangulated-category`.

For the item statement, the Lean rendering is as follows.

* The abelian-category hypothesis is the explicit parameters
  `A : Type u`, `[Category.{v} A]`, and `[Abelian A]`; `[HasDerivedCategory.{w} A]`
  records the common larger localization universe.
* `DF⁺(A)` is `Derived (A := A) false`, with its triangulated structure supplied by
  the `model` field. `omega` and `gr` are functors to `DerivedCategory.Plus A`, and
  the bracketed `CommShift`/`IsTriangulated` fields state exactness of forgetting and
  every graded-piece functor.
* `high` and `low` are the functors `t_{≥p}` and `t_{<p}`. `inclusion`, `quotient`,
  and `connecting` are their natural transformations. `high_comparison` and
  `low_comparison` identify them on representatives with
  `CochainComplex.FiniteFiltered.high false K p` (the filtered subcomplex `F^p K`)
  and `CochainComplex.FiniteFiltered.low false K p` (the quotient `K/F^p K`), while
  `high_normalization` and `low_normalization` pin the maps to the subcomplex
  inclusion and quotient projection.
* `distinguished` renders the natural distinguished triangle. `high_support` and
  `low_support` render the vanishing of graded pieces below `p` and at or above `p`.
  `unique_triangle` renders the unique isomorphism fixing the middle object among
  triangles with those support conditions.
* `high_hom_bijective` and `low_hom_bijective` are exactly the two canonical Hom
  bijections. `high_hom_natural` and `low_hom_natural` give the naturality equations
  in both arguments.
* `grade_truncation` states the canonical natural identification
  `(low (p + 1) ⋙ high p) ⋙ omega ≅ gr p`, i.e. `omega T_p = gr^p`.
  `pure`, `pure_iff`, `place`, `place_equivalence`, `place_forget`, and `place_grade`
  render the pure-grade subcategory, its equivalence with the ordinary bounded-below
  derived category, the inverse placement functor, and the vanishing of all other
  graded pieces (hence acyclic pieces are allowed by `IsZero` in the derived category).

Edge cases checked: `p` outside the finite filtration interval (high or low is zero),
`p` at either endpoint, `p = 0`, a zero complex, an empty/zero graded piece, and
other graded complexes that are acyclic rather than literally zero. The definitions
use integer indices and the localization's derived `IsZero`, so no edge case is
excluded.

Searches made: `rg` over `lean/Sheaf` and the upstream `WeilConjectures` checkout for
filtered localization/truncation declarations; no exact existing package was found.
`msearch.py leanfinder` for “finite filtered derived localization truncation triangle
adjunction pure graded equivalence” returned only ordinary t-structure/localization
hits. `msearch.py loogle` for
`CategoryTheory.Triangulated.TStructure.triangleLTGE, FilteredTruncationData` returned
no match. `msearch.py leansearch` for “finite filtered truncation data exact functors Hom adjunction pure grade” returned only generic exact-functor and ordinary truncation hits. `msearch.py grep` for
`filtered.*truncation|FilteredDerived|FilteredTruncation` found no generic declaration;
the existing Q65 `TruncationCalculus` omits the Hom-adjunction and pure-grade fields,
so the new helper definition is required.

## New nodes

`def-trf-filtered-truncation-data` is added because no node, Mathlib declaration, or
upstream declaration packages all clauses of the universal truncation statement. Its
module and declaration are the structure in `FilteredTruncationData.lean`; the item node now cites it in
`stmt_deps`.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (2026-10-17)

The maintainer's reviewer repaired the helper module `Sheaf.Algebra.Homology.FilteredTruncationData`
and the new node `def-trf-filtered-truncation-data`:

* `omega` and `gr p` were arbitrary exact functors `Derived false ⥤ DerivedCategory.Plus A`.
  The support conditions, the uniqueness clause, the Hom bijections and the pure-grade
  subcategory were therefore stated for unconstrained functors. The new fields
  `omegaComparison : Q false ⋙ omega ⋙ Plus.ι ≅ forget false ⋙ DerivedCategory.Q` and
  `grComparison p : Q false ⋙ gr p ⋙ Plus.ι ≅ graded false p ⋙ DerivedCategory.Q` pin them to
  forgetting the filtration and to `grᵖK = FᵖK/Fᵖ⁺¹K`, in the same way as `TruncationCalculus`.
* `grade_truncation` (the statement's "ω T_p = grᵖ canonically") is now normalized by
  `grade_normalization`. On a representative `K`, the composite
  `ω(t_{≥p}K) → ω(T_pK) ≅ grᵖK` is the canonical projection `complexQuotientπ p (p+1)`.
* The unused import `Sheaf.Algebra.Homology.FiniteFilteredLocalization` is dropped.
  `def-trf-filtered-truncation-data` now cites `lem-trf-filtered-derived-hom-calculus`, whose
  module owns the uniform-filtration localization `CochainComplex.FiniteFiltered.Derived false`
  that the structure uses (`Complex`, `Q`, `forget`, `graded`, `high`, `low`, `highι`, `lowπ`,
  `TriangulatedLocalization`). It no longer cites `def-trf-finite-filtered-localization`, whose
  `FiniteFilteredDerivedPlus` is the termwise or fixed-interval localization and is not used.
