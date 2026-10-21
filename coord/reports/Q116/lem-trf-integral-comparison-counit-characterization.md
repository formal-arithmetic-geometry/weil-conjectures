## Worker report

Item: `lem-trf-integral-comparison-counit-characterization`, group Q116.
Module: `Sheaf.TraceFormula.IntegralComparisonCounitCharacterization`.
The node's statement, proof, and proof dependencies are unchanged. Its statement
dependencies gain the already landed `def-trf-integral-comparison-realization-models`,
whose actual diagonal/limit adjunction, counit, and normalized Roos model are reused.
There are no new nodes and no dependency replacements.

The module contains two theorem statements, each with proof `sorry`, and three
real-data helpers specific to the tower in this item. There are no other postponed
proofs. Every declaration is recorded in `lean.declarations` and tagged with this item.

### Hypotheses and clauses

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The recorded `Padic.coefficientExtensionRing`,
  integral sheaf system, and completed coefficient sheaf supply the valuation ring,
  chosen uniformizer, positive quotients, and actual quotient transitions. No second
  choice of uniformizer or coefficient sheaf is made here.
* Scheme isomorphism: `(h : S ⟶ T) [IsIso h]` in the integral theorem.
  Invertibility of ell is exactly `hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x)`
  and `hT : ∀ y : T, IsUnit (l : T.presheaf.stalk y)`.
* Sites and coefficients: `integralTowerModules l E W` is the existing module
  category over the completed coefficient sheaf on `W.ProEt`. It is not the
  category over the discrete constant integer ring. The generic first theorem
  keeps independent site universe t and extension universe u; its coefficients
  and module sections have size `max u (t+1)`, with site object size t+1 and
  morphism size t. The bounded constructible clause uses the recorded
  `sfIntegralConstructible` presentation, with scheme and field in its common
  universe u; no replacement constructibility predicate is introduced.
* Module sheaves and unbounded derived categories: `integralTowerModules`,
  `DerivedCategory`, and `coefficientSequenceRestrictedDerived` are the existing
  categories. Their complexes are ℤ-indexed, without boundedness hypotheses.
* Positive-index strict towers: `ℕᵒᵖ ⥤ integralTowerModules l E X`; index n is
  the paper's positive exponent n+1. `integralComparisonConstantTower` is exactly
  `(Functor.const ℕᵒᵖ).mapDerivedCategory`, not an arbitrary diagonal functor.
* For every H and every derived tower T, the first conjunct of
  `integralComparisonLimitCounitCharacterization` asserts `Function.Bijective`
  for `fun f ↦ Delta.map f ≫ (integralComparisonTowerCounit ...).app T`.
  This is precisely the displayed Phi, with Lean composition written left to right.
* Naturality in both derived variables is the second conjunct, quantified over
  arbitrary derived maps `a : H' ⟶ H`, `b : T ⟶ T'`, and `f`. It says that
  Phi(a f Rlim(b)) = Delta(a) Phi(f) b. In particular b need not be a strict
  chain map or a separately supplied family of finite-level maps.
* The K-injective resolution and injective terms occur in the final conjunct:
  `j : T ⟶ I`, `[QuasiIso j]`, `[I.IsKInjective]`, and
  `_hI : ∀ p : ℤ, Injective (I.X p)`.
* Computation of Rlim on I is the existing
  `Functor.rightDerivedFunctorObjQIso lim I`. Its target is the localization of
  the termwise ordinary limit. The last equation transports Rlim(T) to that
  model by `Rlim(Q.map j)`, applies the exact-diagonal localization factor, the
  ordinary projection counit `NatTrans.mapHomologicalComplex constLimAdj.counit`,
  and finally `inv (Q.map j)`. This is epsilon_T as stated in the node.
* Independence of resolution is expressed by quantifying this same formula over
  every j and identifying every result with the same natural derived counit.
  Thus two resolutions give the same Hom map under their canonical
  right-derived identifications. No equality of separately evaluated projections
  is used to express this independence.
* Bounded constructible complete K is `_hK : sfIntegralConstructible l E T
  (DerivedCategory.Q.obj K)`. Taking a complex representative K loses no derived
  objects, since Q is essentially surjective. This is the recorded condition of
  derived completeness, constructible reductions, and one uniform finite interval.
* The chosen flat-term K-flat resolution is
  `P : (integralOperationsGoodComplex l E T).FullSubcategory` and
  `q : P.obj ⟶ K` with `[QuasiIso q]`. GoodComplex is exactly the recorded
  independent-coefficient K-flat predicate plus flatness of every term; no
  arbitrary model of the reduction or extra exactness assumption is supplied.
* Actual P_m, restricted finite pullbacks C_g,m, and quotient transitions are
  `(integralOperationsPullbackTowerFunctor l E h).obj P.obj`.
  `integralComparisonPullbackStrictTower` applies the existing
  `HomologicalComplex.functorEquivalence.inverse` to this actual tower, placing
  it in complexes of towers without changing its objects or arrows.
* Actual theta_m is `inverseImageReductionTheta`, already normalized by the
  sectionwise reduction and sheafified tensor unit. `integralComparisonThetaStrictTower`
  uses `NatTrans.ofOpSequence` with its recorded strict compatibility theorem,
  then the same existing complexes/diagrams equivalence. Thus it is the entire
  strict family theta^Delta, not an arbitrary arrow with unspecified components.
* The chosen normalized Roos identification is `ρ : IntegralComparisonRoosModel`.
  Its `comparison` is natural on all strict complexes and its `computes` field
  fixes it on K-injectives by the ordinary zero-shifted-coordinate inclusion.
  It is the already defined normalized model; this delivery introduces no
  arbitrary cone isomorphism or weakened Roos interface.
* `integralComparisonPullbackLimitIso` identifies Lh*Q(K) with Rlim C_g.
  It first inverts Lh*(Qq), then uses the existing defining pullback comparison
  on P, and finally the inverse normalized Roos comparison on the actual tower.
  All three are actual existing isomorphisms and all data of this helper are explicit.
* The first conjunct of `integralComparisonCounitCharacterization` is an iff
  quantified over every candidate f. Its left side is exactly
  epsilon_C Delta(f) = theta^Delta Delta([h inverse(q)] inverse), after the
  just-described target identification and the required exact-functor
  localization factors. Its right side is f equal to the specified
  `inverseImagePullbackComparison ... K P q`. Hence existence and uniqueness
  are both stated, with the specified map as the unique solution.
* The second conjunct gives the explicit zero shifted-product description:
  the specified map, followed by the target identification, is the inverse
  localized inverse-image resolution followed by
  `Q.map (inverseImageRoosComparisonComplex ... P.obj)` and the inverse Roos
  identification. That existing chain map is literally `mappingCocone.lift`
  with first component the actual theta product and zero homotopy.

### Dependency declarations read and used

* `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, retaining the coefficient constructors.
* `def-weil-scheme-morphism-properties`: convention-only record, no declaration;
  schemes, `IsIso`, and stalkwise `IsUnit` express the specified conditions.
* `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and its topology.
* `def-weil-completed-integral-coefficients`:
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
  `WeilConjectures.integralConstantToCompletionOfUniverses`, publicly retaining
  `completedIntegralCoefficientSheafUnrestricted` and its actual projections.
* `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, the transparent `SheafOfModules` specialization.
* `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and Q.
* `def-weil-inverse-system`: `Mathlib.CategoryTheory.Functor.OfSequence`,
  `Functor.ofOpSequence` and `NatTrans.ofOpSequence`.
* `lem-weil-tower-category-levelwise-abelian`: Mathlib match
  `CategoryTheory.Abelian.functorCategoryAbelian` in
  `Mathlib.CategoryTheory.Abelian.FunctorCategory`; inherited levelwise structures.
* `def-pur-kinjective-complex`: Mathlib match `CochainComplex.IsKInjective`
  in `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
* `def-sp-injective-resolutions`: `CategoryTheory.Injective` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`; the item needs injective
  tower terms, not an object-level nonnegative injective resolution.
* `lem-weil-pbc-ringed-strict-tower-homotopy-limit`:
  `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`;
  the existing realization-model module reuses the total right-derived functor.
* `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`,
  `WeilConjectures.sfIntegralConstructible`.
* `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, inside GoodComplex.
* `lem-pc-kflat-resolution`:
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`; imported
  through the recorded derived-comparison dependency, retaining its chosen resolution.
* `def-weil-inverse-image-pullback-comparison`:
  `Sheaf.Paper.InverseImagePullbackComparisonDerived`, publicly retaining
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparison`,
  `inverseImageReductionTheta`, `inverseImageReductionTheta_compatible`,
  `inverseImageRoosComparisonComplex`, and the exact inverse-image functors.
  The primary derived-object wrapper is unnecessary because the node explicitly
  chooses the representative and q; the same recorded underlying construction is used.
* `lem-weil-strict-roos-comparison`: `Sheaf.CategoryTheory.StrictRoosComparison`,
  `CategoryTheory.strictRoosComparison`; normalized comparison with the ordinary
  limit inclusion, whole strict augmentations, and resolution transport.
* `def-pur-sheaf-inverse-limit`: Mathlib `CategoryTheory.Limits.limit` and `limit.π`.
* Proof-only `lem-weil-pbc-termwise-adjunction-homotopy`:
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`,
  `CategoryTheory.Adjunction.mapHomotopyCategory`.
* Proof-only `lem-pc-pre-derived-adjoint-functors-general`:
  `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`,
  `CategoryTheory.preDerivedAdjunctionGeneral`.
* Proof-only `lem-weil-proetale-countable-products-exact`:
  `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
  `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`.
* Newly cited, already landed `def-trf-integral-comparison-realization-models`:
  `Sheaf.Paper.IntegralComparisonRealizationModels`,
  `WeilConjectures.integralComparisonConstantTower`,
  `integralComparisonConstantAdjunction`, `integralComparisonTowerCounit`,
  `integralComparisonTowerCounit_computes`, `IntegralComparisonRoosModel`.

### Edge cases

Checked before drafting: K=0 and arbitrary zero H/T introduce no exceptional
denominators; q and j remain quasi-isomorphisms and their Q-images invertible.
For a constant tower the ordinary counit is its family of projections, as required.
For h=id the specified comparison is the completion comparison and is not silently
replaced by an identity. The least positive quotient m=1 is Lean n=0. The empty
scheme is permitted; the stalkwise unit hypotheses are then vacuous as they should
be. H and T may be unbounded. Tower maps in the naturality clause are arbitrary
derived maps. The resolution formula covers j=id whenever its complex has the
required K-injectivity and injective terms, and covers every other resolution too.
No countable-product exactness is imposed in the Hom-bijection theorem.

### Searches and source checks

* `msearch.py ... leanfinder "Derived constant inverse tower and inverse limit
  adjunction with K-injective counit"`: eight hits, principally
  `CategoryTheory.Adjunction.derived'_counit`, `derived_counit`, and derived-zero
  comparison identities. None state the whole integral comparison characterization.
* `msearch.py ... loogle "CategoryTheory.Limits.constLimAdj,
  CategoryTheory.Adjunction.derived"`: no hits for that combined query.
* `msearch.py ... grep "counit.*[Tt]ower|[Tt]ower.*[Aa]djunction|constLimAdj"
  CategoryTheory`: nine ordinary-limit/localization hits. `constLimAdj` is the
  ordinary adjunction and is reused through the existing realization definitions.
* `rg` on `lean/WeilConjectures` and `lean/Sheaf` for integral/constant-tower
  counits, constantTower, and this item id found the reusable realization models,
  `IntegralConeCounitRealization`, and `IntegralPullbackReductionCounit`.
  The cone theorem takes the supplied normalized cone data but does not give this
  Hom bijection or characterize this specified kappa after q is inverted. The
  reduction-counit theorem expresses a different whole-system reduction equation.
  Neither is an exact existing match for this node. No existing declaration
  uses the five new full names.
* `grep -rn` for this node id in `lean/WeilConjectures`: no match.
* Read the exact signatures and docstrings of the recorded dependencies and
  their publicly retained constructions. Read Stacks `derived.tex`, labels
  `lemma-pre-derived-adjoint-functors-general` and
  `lemma-pre-derived-adjoint-functors` (0FND, 0DVC), and `sites-cohomology.tex`,
  `lemma-derived-limit-is-ok` (0941). Read current blueprint Global powers.

Compilation: `scompile.py Q116 lem-trf-integral-comparison-counit-characterization
<module>` succeeded for both the sandbox module and its final library name,
23.8 s and 17.5 s respectively, without errors or warnings. One initial
elaboration failure in the strict-family constructor was repaired by reducing
the actual `ofOpSequence` transition using the recorded compatibility theorem.
No source statement was changed. All compilation used the prescribed wrapper.

## Second reading by Q116

I reread the node, both theorem signatures, and all three helper definitions after
the clean compile. The first theorem quantifies over the entire derived tower
category, not only strict morphisms. Its counit formula uses the ordinary termwise
limit and inverts j only after localization, with the exact-diagonal factor in the
correct direction. Equality with a single counit for every j records resolution
independence. The second theorem retains the required constructibility hypothesis,
the chosen good resolution, both stalkwise invertibility hypotheses, and the actual
coefficient transitions. The theta constructor uses the already normalized section
maps. The candidate f has exactly the source and target of the specified kappa.
Its equality is in the derived category of whole towers; finite-level evaluations
are never used as a replacement. The target is transported by the defining
pullback comparison and normalized Roos model, and the last conjunct is precisely
the zero-homotopy cone formula. All added helpers have real data and the only two
`sorry` proofs correspond to the two clauses of this same DAG node. No additional
mathematical mismatch was found during this rereading. This is a self-audit;
the dispatcher's separately performed maintainer review remains independent.
