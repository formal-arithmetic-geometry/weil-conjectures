## Worker report

The module `Sheaf.CategoryTheory.FiniteModelRestrictionComparison` states
`CategoryTheory.FiniteExactComplex.finite_model_restriction_comparison` and supplies three
concrete helpers owned by this same comparison node. The theorem proof is `sorry`; none of
the definitions has sorry data or an embedded postponed proof. There are no new DAG nodes,
no dependency repairs, and no statement correction.

Hypothesis and clause correspondence:

- Four abelian categories: the explicitly universe-bound `A`, `A'`, `B`, `B'`, each with
  `[Category] [Abelian]`. Each has its own `[HasDerivedCategory]` and independent localization
  morphism universe. Enough injectives are `[EnoughInjectives A] [EnoughInjectives A']`.
- Additive left exact `G,G'`: their functor binders, `[G.Additive]`, `[G'.Additive]` and
  `PreservesFiniteLimits`. Their ordinary total derived pairs are `RG,η` and `RG',η'` with
  Mathlib's `IsRightDerivedFunctor` universal-property classes. Computation by bounded-below
  injective resolutions is `hη,hη'`: the unit is invertible on every such injective complex.
  This interface is also the recorded finite-model dependency's interface; it imposes no
  existence assumption about unbounded K-injective resolutions.
- The common finite interval `[0,r]`: `r : ℕ`, functors into integer cochain complexes,
  and `hF,hF'` asserting zero terms outside `0 ≤ a ≤ r`. All degree functors are exact via
  `hExact,hExact'`, preserving finite limits and colimits. Additivity is explicitly bound
  on F,F'; it is already implied by the stated exact degree functors, and is the standard
  interface used by the dependency. No choice of a skeleton or literal zero terms is made.
- Natural augmentations are `e,e'`; injective quasi-isomorphism conditions are `he,he'`.
  `normalizedModelComparison` extracts exactly the existential natural isomorphism from
  `finite_exact_complex_derived_model` with these arguments. Its every-resolution formula
  determines the chosen object up to equality, so this choice satisfies the permitted
  universal-property/unique-characterization exception, rather than choosing unknown data.
- Exact additive U,V: their additive, finite-limit and finite-colimit instances. The given
  natural isomorphisms are `γ : U ⋙ G ≅ G' ⋙ V` and
  `θ : U ⋙ F ≅ F' ⋙ V.mapHomologicalComplex (.up ℤ)`. The per-object chain-map equation
  `hcompat` is precisely `theta e_U = V(e') gamma[0]`, including the inverse canonical
  `singleMapHomologicalComplex` transport at G'X. `V.mapDerivedCategory` is the induced D(V).
- Nonnegative injective resolutions: all `X,J,hJ,hJinj,t,[QuasiIso t]` and
  `I,hI,hIinj,s,[QuasiIso s]` are universally quantified in the conclusion. These are the
  actual integer complexes in the node, not an extra bundled selection of resolutions.
  Injectivity and quasi-isomorphism are the recorded Mathlib notions. This avoids changing
  the objects to the dependency's optional natural-number-indexed bundled interface.
- `restrictedAugmentation U t` is the real chain map Ut: canonical transport from UX[0]
  to U(X[0]), followed by degreewise U(t). Existence is the first conjunct under each
  resolution pair: `∃ β, restrictedAugmentation U t ≫ β = s`.
- The next conjunct quantifies over every pair β₁,β₂ satisfying this literal equality and
  asserts `Nonempty (Homotopy β₁ β₂)` and equality after applying degreewise G and Q.
- The third conjunct quantifies over every extension β and asserts `QuasiIso (G.map… β)`.
  Write R for `(resolutionComparison G RG η s …).hom`, R' for its primed analogue,
  C for `Q.map (restrictionComplexComparison … J).inv`, and P for the canonical factor
  `V.mapDerivedCategoryFactors.hom.app (G'(J))`. The subsequent equation is
  `R = α_X ≫ D(V).map R' ≫ P ≫ C ≫ QG(β)`.
  Since QG(β), R', P and C are invertible, this is exactly the node's displayed formula
  for α, with multiplication by those invertible factors instead of syntax requiring
  an IsIso instance from a preceding conjunct. `restrictionComplexComparison` is γ_J
  transported through Mathlib's degreewise composition isomorphisms, so C is γ_J inverse.
- A single `∃! α` is a natural isomorphism from `U ⋙ singleFunctor A 0 ⋙ RG` to
  `singleFunctor A' 0 ⋙ RG' ⋙ V.mapDerivedCategory`. Its one value works for every choice
  of t,s,β, expressing independence of resolutions and extensions. Being a natural
  isomorphism includes the node's naturality in every morphism X→Y. Uniqueness is not a
  stronger mathematical claim: the node's finite-model equation forces α uniquely.
- The first global equation is
  `λ_U ≫ α_X = Q(θ_X) ≫ V.mapDerivedCategoryFactors.inv.app (F'X) ≫ D(V).map λ'_X`.
  This is exactly the finite-model equation in the node, with the localization transport
  from Q(VF'X) to D(V)(QF'X) explicit.
- The last equation is
  `α_X inverse ≫ RG.map Q(Ut) = D(V).map R' ≫ P ≫ C ≫ η_(UJ)`.
  RG(Q(Ut)) is invertible because U is exact and t is a quasi-isomorphism. Thus this is
  precisely the displayed inverse-unit formula in node proof step 8, multiplied on the
  right by that invertible map. It uses the actual derived unit on UJ, without assuming
  UJ consists of injectives. No preservation of injectives by U is present anywhere.

Dependency interfaces read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `Injective`, `EnoughInjectives`, `InjectiveResolution`; the resolution is represented
  by its constituent integer complex and augmentation, as in the finite-model interface.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`, unit, universal property, uniqueness,
  unit invertibility and object comparison were read. As in the finite-model dependency,
  the statement uses an arbitrary universal pair instead of selecting this construction,
  whose separate unbounded K-injective-existence premise the item does not assume.
  This module is publicly imported through the finite-model module. The universal pair
  is expressed by `Mathlib.CategoryTheory.Functor.Derived.RightDerived.IsRightDerivedFunctor`.
- `Sheaf.CategoryTheory.FiniteExactComplexDerivedModel`:
  `finite_exact_complex_derived_model` and `resolutionComparison`, with the full signatures
  and docstrings read. The former supplies the normalized lambdas; the latter is exactly
  `RG(Qs)` followed by the inverse of the specified unit component.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, Q.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `mapDerivedCategory` and
  `mapDerivedCategoryFactors`; `Mathlib.Algebra.Homology.Additive` supplies
  `NatIso.mapHomologicalComplex` and `Functor.mapHomologicalComplexCompIso`.

Proof-dependency imports are retained for stage 3: the adopted
`WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy` (recorded
`CochainComplex.homotopy_of_comp_quasiIso_of_injective`),
`WeilConjectures.Algebra.Homology.FiniteStripAugmentation` (recorded
`HomologicalComplex₂.quasiIso_of_finite_strip_row_augmentation`), Mathlib's
`ModelCategory.Injective` (the recorded lifting-property instance), and
`ShortComplex.PreservesHomology` (`Functor.homologyFunctorIso`). The recorded double
complex module `WeilConjectures.CategoryTheory.DoubleComplexTotal` is publicly imported
through the finite-model module; its actual finite total convention was read.

Edge cases checked before writing and again against the complete signature:

- r=0 is included, as are zero categories, zero objects and resolutions with zero terms;
  the support condition uses IsZero rather than definitional equality to a selected zero.
- Negative degrees are expressly zero in resolutions and both finite models, but there
  is no artificial upper bound on resolutions. All β are covered, including zero maps
  when forced by zero objects.
- Identity functors and identity ordinary/model comparisons are allowed. Under these
  specializations the equations reduce to the normalized identity comparison from the
  dependency; no nonidentity or arbitrary-lift case is discarded.
- U need not preserve injectives: the signature has no such instance. Its exactness
  is used for Ut, not for termwise injectivity of UJ. V has no faithfulness assumption.
- Object, morphism and derived localization universes for all four categories are
  independent. There is no equality between site or category universes.

Searches (2026-10-24):

- `msearch.py NN lem-sfb-finite-model-restriction-comparison leanfinder` with query
  "Exact restriction comparison between total right derived functors computed by finite
  exact cochain models, normalized by the derived unit": OK, eight hits, including
  `LocalizerMorphism.rightDerivedFunctorComparison`, `mapDerivedCategoryFactors`, and
  generic total-right-derived results. None contains the finite-model hypotheses,
  every-extension quasi-isomorphism/homotopy assertions, and both normalizations here.
- `msearch.py ... loogle` query
  `CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.Functor.IsRightDerivedFunctor`:
  OK, zero hits.
- `msearch.py ... grep` query `finite.*model.*restriction|restriction.*finite.*model`,
  subdirectory `CategoryTheory`: OK, zero hits.
- `rg` of project Sheaf and WeilConjectures for the node id, finite_model_restriction,
  FiniteModelRestriction, and the proposed helper names: no existing declarations.
  Broader restriction/comparison search found specialized coefficient comparisons,
  not this categorical statement. Mathlib rg located the degreewise, derived-exact and
  localization comparison constructions which are reused, rather than redefined.
- Read the current `literature/blueprint/latest` direct-image proof paragraph (3), and
  Stacks `derived.tex` lemmas morphisms-lift (013P), morphisms-equal-up-to-homotopy (013S),
  alongside the recorded finite-model proof and totalization source conventions.

Validation: `scompile.py NN lem-sfb-finite-model-restriction-comparison <module>` passes
both sandbox and library module checks cleanly, approximately six seconds each. The sole
postponed result is the main theorem, with its eight-step natural-language proof in its
docstring. No STATEMENT-DISPUTED or node fault was found.

## Second reading by NN

A separate rereading pass compared the complete node text and all eight proof steps with
the written signature and the full helper bodies. No additional worker was started, in
accordance with the dispatcher instruction; the maintainer supplies the independent review.
The resolution-formula check caught an initial reversal: QG(β) cannot be composed after
ρ_s. It was repaired to `ρ_s = α DV(ρ'_t) P Q(γ_J)^(-1) QG(β)`, which is equivalent to
the original formula because the theorem also asserts G(β) is a quasi-isomorphism.
The explicit NatIso mapping API was also corrected during compilation. The final reading
checked the ordinary augmentation transport, both directions of the localization factor,
the unit at UJ rather than at an assumed injective UJ, both universal resolution binders,
the pairwise homotopy clause, and the natural finite-model equation. All clauses now match;
the source statement and DAG dependencies require no change.
