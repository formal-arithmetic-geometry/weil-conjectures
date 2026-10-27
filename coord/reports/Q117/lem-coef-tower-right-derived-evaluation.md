## Worker report

Item: `lem-coef-tower-right-derived-evaluation`, group Q117. The module
`Sheaf.CategoryTheory.TowerRightDerivedEvaluation` states
`CategoryTheory.TowerRightDerivedEvaluation.exists_normalized`, with `sorry` as its whole
proof. Its only other declaration, `cochainUnit`, is a real-data helper expressing the
recorded homotopy-level universal unit on cochain complexes. It composes the existing
quotient/localization factor isomorphisms and the existing universal unit. It chooses no
new derived functor, resolution, comparison, or arbitrary map. No new DAG node, dependency
repair, statement correction, or disputed statement is needed. Only `lean` changes in the
item's node copy.

### Hypotheses and clauses

- Abelian categories A and B: independent `{A : Type uA}`, `{B : Type uB}`,
  `[Category.{vA} A]`, `[Category.{vB} B]`, `[Abelian A]`, `[Abelian B]`.
- Additive F: `(F : A ⥤ B) [F.Additive]`. No further property of F is bound.
- Towers and their transitions: `ℕᵒᵖ ⥤ A` and `ℕᵒᵖ ⥤ B`; the functor
  `(Functor.whiskeringRight ℕᵒᵖ A B).obj F` applies F to objects and actual transitions.
  As in the recorded inverse-system interface, index n means positive level n+1.
- Ordinary unbounded derived categories: `DerivedCategory` with four independently sized
  `[HasDerivedCategory.{wA} A]`, `[HasDerivedCategory.{wB} B]`,
  `[HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]`, and
  `[HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]`. Complexes have degree type ℤ throughout.
- Precisely the two existence assumptions: `enough` quantifies over every cochain complex
  of A and `enoughT` over every tower complex. Each asks for a map to I with
  `I.IsKInjective ∧ QuasiIso a`, with no mono condition. Mathlib's `IsKInjective` is exactly
  null-homotopy of every map from an acyclic complex, not merely termwise injectivity.
- The two total right derived functors and universal units are the already recorded
  `F.rightDerivedFunctorOfQuasiIsoResolutions enough` and its tower counterpart using
  `enoughT`. Their units and universal properties are supplied by the dependency's
  `rightDerivedFunctorOfQuasiIsoResolutionsUnit` and
  `rightDerivedFunctorOfQuasiIsoResolutions_universal`. Thus no additional derived-functor
  existence hypothesis is imposed; the statement uses the canonical universal pairs.
- Specified derived comparisons: `∃ β : ∀ n : ℕᵒᵖ, RT ⋙ E_B(n).mapDerivedCategory ≅
  E_A(n).mapDerivedCategory ⋙ RF`, with RT and RF written out in the file. This is a
  natural isomorphism of unbounded derived functors, not a family of homology isomorphisms.
- Unit equation for every complex P: the first conjunction says that the inverse output
  evaluation localization factor, evaluated tower unit, beta at QP, and RF of the input
  evaluation localization factor compose to the evaluated ordinary unit. The helper
  `cochainUnit` converts the recorded homotopy unit by `quotientCompQhIso` and
  `mapHomotopyCategoryFactors`, retaining every canonical identification.
- Every K-injective resolution: the second conjunction quantifies over all n, P, I, a,
  `[I.IsKInjective]`, and `[QuasiIso a]`. Its existential proofs `hI` and `ha` assert,
  respectively, that the evaluated I is K-injective and the evaluated a is a
  quasi-isomorphism. They are passed explicitly to the existing resolution isomorphism,
  so they impose no extra hypothesis on the input.
- Identification through Q(F(I_n)): in the same second conjunction, the left side is
  beta at QP followed by RF of the input localization factor and the existing comparison
  `F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough a_n`. The right side is output
  evaluation of `FT.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughT a`, followed by
  its evaluation localization factor. Both sides end at the same actual Q(F(I_n));
  strict termwise evaluation makes this endpoint definitionally identical. Cancelling
  the input comparison is the node's formula beta = (cF) inverse composed with e_n(cT),
  including the displayed localization factors.
- Resolution independence: the same beta is selected outside the quantifier over every
  resolution, and the equation identifies its value for each choice. Proofs hI and ha
  are propositions, so their witnesses cannot introduce dependence on proof choices.
- Naturality for every derived morphism: beta is a `NatIso` on the full derived category,
  which includes all localization morphisms, not just images of complex maps.
- Actual transition equation: the final conjunction quantifies over all m, n, all
  `(t : m ⟶ n)`, and every derived tower M. It states
  `transition_B(t).app (RT.obj M) ≫ beta_n =
  beta_m ≫ RF.map (transition_A(t).app M)`, exactly the requested equation in Lean's
  left-to-right composition convention. Both transitions use the dependency's
  `towerDerivedEvaluationTransition`; no arbitrary comparison map is substituted.
- Identity and composite transitions are included because t ranges over every arrow,
  including identity arrows and t followed by another actual tower arrow. No left
  adjoint, boundedness, Grothendieck-category, injective-terms, or product-exactness
  condition appears.

### Recorded dependency declarations read and used

Statement dependencies:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; tower abelianness uses
  `CategoryTheory.Abelian.functorCategoryAbelian` from
  `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `def-weil-pbc-additive-functor`: `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
- `def-weil-inverse-system`: `CategoryTheory.Functor.ofOpSequence` and
  `CategoryTheory.NatTrans.ofOpSequence`, `Mathlib.CategoryTheory.Functor.OfSequence`;
  the statement uses the recorded equivalent functor-category encoding.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, and `DerivedCategory.Qh`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-sfb-right-derived-functor`: the functor, unit, universal property and
  `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`, namespace `CategoryTheory.Functor`,
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
- `def-coef-tower-derived-evaluation-transition`:
  `CategoryTheory.towerDerivedEvaluationTransition`,
  `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`. Its definition uses
  `Localization.liftNatTrans` of the actual tower-arrow transformation.

Proof dependencies, imported plainly where not already exposed by statement imports:

- `lem-weil-tower-category-levelwise-abelian`: Mathlib functor-category abelianness and
  exact evaluation (the recorded Mathlib match).
- `lem-weil-pbc-exact-functor-derived-factorization`:
  `Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `lem-weil-pbc-kinjective-total-derived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`,
  `Sheaf.CategoryTheory.KInjectiveTotalDerived` (publicly imported by the recorded
  right-derived-functor module).
- `lem-weil-tower-evaluation-kinjective`:
  `CategoryTheory.tower_evaluation_isKInjective`,
  `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`.
- `lem-weil-pbc-kinjective-exact-square-comparison`:
  `CategoryTheory.KInjectiveExactSquare.existsUnique_normalized`,
  `Sheaf.CategoryTheory.KInjectiveExactSquareComparison`.
- `lem-sf-kinjective-derived-map-computation`:
  `CategoryTheory.Functor.kInjectiveDerivedMapComputation` and its functorial and
  change-of-resolution declarations, `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`.

All recorded statement interfaces and their docstrings were read. The theorem docstring
carries all six proof steps, including application of the existing exact-square theorem
instead of reconstructing that result.

### Edge cases and source check

Read the exact-left-adjoint paragraph of `literature/stacks-project/sites-cohomology.tex`,
Tag 0941, `lemma-derived-limit-is-ok`, especially the finite-support tower left adjoint
and its preservation of K-injectivity. This is a categorical generalization of that
paragraph, exactly as the reviewed node specifies.

Checked: the first positive level (op 0), m=n, composite transitions, zero complex, zero
functor, and an arbitrary additive functor that is not left exact. In particular the
comparison never claims F(I_n) itself is K-injective. No infinite products occur in any
construction, so no product-exactness assumption is implicit. The site/category and
localization universes remain independent; no equality is added to satisfy an API.

### Searches and validation

Used the prescribed `msearch.py` wrappers (raw records are in `searches.jsonl`):

- LeanFinder: `Total right derived additive functor on inverse towers commutes with
  evaluation and universal units using K injective resolutions`; eight hits, finite-degree
  right derivation and exact localization factors, no matching theorem.
- Loogle: `CategoryTheory.Functor.IsRightDerivedFunctor`; twelve hits, generic universal
  properties and uniqueness, no tower-evaluation statement.
- Mathlib grep: `evaluation.*rightDerived|rightDerived.*evaluation|
  evaluation.*totalRightDerived|totalRightDerived.*evaluation`; zero hits.
- LeanSearch: `Unbounded total right derived additive functor on inverse systems commutes
  with evaluation with units and transitions`; eight hits, finite-degree right derivation
  and the generic total-right-derived construction, no matching comparison.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for the
  item id and right-derived/evaluation combinations, plus the prescribed `grep -rn` of
  the item id in `lean/WeilConjectures`: no matching existing theorem.
- Read the nearest match `exists_unique_towerDerivedEvaluation_normalized` in the
  transition's module. It requires Grothendieck categories and an exact-left-adjoint
  presentation, unlike this item's arbitrary additive F. Its transition construction
  is reused, but its theorem cannot replace this statement.
- Checked cochain-unit helpers: `UnboundedExactTower.cochainUnit` realizes a different
  recorded derived functor requiring monomorphic resolutions. The new helper merely
  realizes the already recorded arbitrary-quasi-isomorphism universal unit and does not
  redefine that functor or its unit.

`scompile.py Q117 lem-coef-tower-right-derived-evaluation <module>` passed the sandbox
compile (4.8 s) and actual module-path compile (5.3 s), each within the unchanged 60 s
limit, with no errors or warnings. Diagnostic `#check` commands were removed. The single
postponed theorem is `CategoryTheory.TowerRightDerivedEvaluation.exists_normalized`.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
