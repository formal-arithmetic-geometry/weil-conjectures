## Worker report

The module `Sheaf.Algebra.Homology.FilteredHomComplexInvariance` states the concrete
invariance lemma for integer indexed cochain complexes in an abelian category. It uses
Mathlib's `CochainComplex.HomComplex` for
`C(P,I)^n = HomComplex.Cochain P.obj I.obj n`; its differential is the existing
`HomComplex.δ` differential, whose component formula is the stated
`d_I f - (-1)^n f d_P`. The helper definitions are:

- `FilteredHomotopy`, which requires a Mathlib `Homotopy` and a lift through every
  filtration step in every pair of cochain degrees.
- `ShiftFilteredHomCondition`, rendering
  `f^i(F^a P^i) ⊆ F^(a+r) I^(i+n)` component by component.
- `IsShiftFilteredHomFiltration`, requiring membership in each filtration step to be
  equivalent to that shift condition.
- `IsPrecompositionMap` and `IsPostcompositionMap`, which render the component formulas
  `(s^*f)^i = f^i s^i` and `(u_*f)^i = u^(i+n) f^i`.
- `IsFilteredHomotopyEquivalenceMap`, which renders filtered homotopy inverses.

The main theorem is `CategoryTheory.filtered_hom_complex_invariance`. Its hypotheses
are exactly the abelian category, finite filtrations, bounded `P` and `P'`, bounded-below
`I` and `J`, and injectivity of every graded term of `I`:

- `hP` and `hP'` bind uniform finite filtration and two-sided cochain-degree bounds.
- `hI` and `hJ` bind uniform finite filtration and lower cochain-degree bounds.
- `hIinj` is `∀ a n, Injective ((I.filtration.gradedPiece a).X n)`.

The conclusion supplies the shift filtrations for `C(P,I)`, `C(P',I)`, and `C(P,J)`,
proves their uniform finiteness and lower bounds, supplies componentwise filtered
precomposition and postcomposition maps, states filtered-homotopy invariance in each
variable, states that filtered homotopy equivalences induce filtered homotopy
 equivalences, and states that precomposition by a graded quasi-isomorphism is a graded
quasi-isomorphism. The map formulas are carried by `IsPrecompositionMap` and
`IsPostcompositionMap`; the graded clauses use
`FilteredObject.gradedMapSteps` and Mathlib `QuasiIso`.

Dependency declarations used:

- `def-sp-abelian`: Mathlib `CategoryTheory.Abelian` from
  `Mathlib.CategoryTheory.Abelian.Basic`.
- `def-weil-abstract-derived-category`: Mathlib `DerivedCategory` from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the Hom-complex calculation uses
  the same integer cochain-complex conventions.
- `def-sp-filtration`: upstream `CategoryTheory.DecreasingFiltration` from
  `WeilConjectures.CategoryTheory.Abelian.Filtration`, with the compatibility API in
  `Sheaf.CategoryTheory.Filtration`.
- `def-sp-filtered-complex-subquotients`: `CategoryTheory.DecreasingFiltration.complexCycles`
  and the associated existing subquotient module
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients`.
- `def-sp-injective-resolutions`: Mathlib `CategoryTheory.Injective` from
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
- The existing project declaration
  `CategoryTheory.FilteredObject.gradedMapSteps` is imported from
  `Sheaf.CategoryTheory.FiniteFiltrationInduction` for the graded-map clauses.

Edge cases checked before writing the statement were the zero complex, a single
filtration grade, and filtration shifts `r` outside the finite interval. The existential
lift formulation makes the zero and empty-step cases meaningful, while the explicit
uniform bounds do not depend on cochain degree. The integer index type is fixed to
`ℤ`, and all category and universe variables are explicit (`autoImplicit false`).

Searches made:

- `msearch.py ... leanfinder "The filtered Hom complex is invariant under filtered
  homotopies and filtered quasi-isomorphisms in the source and target"`: eight hits,
  all ordinary homotopy/localization results; no shift-filtered Hom result.
- `msearch.py ... loogle "HomComplex, Homotopy, QuasiIso"`: no hit (unknown identifier
  in the loogle query); direct Mathlib inspection found `CochainComplex.HomComplex`.
- `msearch.py ... grep "filtered.*Hom.*quasi|Hom.*filtered.*homotop"
  Algebra/Homology`: zero hits.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` found the existing unfiltered
  `HomComplex`, filtration/subquotient APIs, and no declaration of this filtered
  invariance theorem.

No `STATEMENT-DISPUTED` flag and no node correction were needed. No new definition node
or dependency repair module was needed.

## Second reading by Q118

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (cc reviewer, 2026-10-17)

- H3: the injectivity hypothesis `hIinj` on the graded terms of `I` was a hypothesis of the
  whole theorem, so the shift filtrations, the pre-/postcomposition maps, both homotopy
  invariance clauses and the homotopy-equivalence clauses were only stated for targets `I`
  with injective graded terms. The node assumes it only for the graded quasi-isomorphism
  clause ("Suppose each gr^a I^n is injective ... If s is a graded quasi-isomorphism ...").
  The hypothesis now guards only that last clause:
  `(∀ a n : ℤ, Injective ((I.filtration.gradedPiece a).X n)) → ∀ s : P' ⟶ P, ...`.
- H8: `IsPrecompositionMap`, `IsPostcompositionMap` and `IsFilteredHomotopyEquivalenceMap`
  now carry source places and `(blueprint: lem-trf-filtered-hom-complex-invariance)`; the
  module docstring names the graded quasi-isomorphism clause.
- `lean.declarations` lists the six helper predicates with the main theorem; `lean.statement`
  is the new signature verbatim.
