/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.RoosAdjunctionQuotientNormalization
public import WeilConjectures.AlgebraicGeometry.PrimitiveQuotientRealizationComparisons
public import WeilConjectures.AlgebraicGeometry.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.AlgebraicGeometry.IntegralComparisonSequenceSystems
import WeilConjectures.CategoryTheory.SystemScalarCoherence
import WeilConjectures.AlgebraicGeometry.TransportedReductionSystemsNormalized
import WeilConjectures.AlgebraicGeometry.PrimitiveQuotientRealizationsUnique
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionConstructibleIntrinsic
import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined

/-! # Effectivity and simultaneous descent of quotient realization models

Source: Stacks Project, sites-cohomology.tex, Tags 0941 and 06YS; current blueprint,
sec-trace-formula/sk-thm-tf-uniform-formula, integral transport paragraph.
(blueprint: lem-trf-effective-quotient-model-descent).

The ambient assertions keep independent site and coefficient universes. In the
constructibility assertion, u is a common bound for schemes and coefficient fields,
as in the recorded intrinsic constructibility predicate. The small site still has
objects in Type (u+1) and morphisms in Type u. Level n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard CategoryTheory.constantSheaf
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.integralOperationsRoosFunctor WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.sfIntegralConstructible

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ambient normalization, actual reconstruction maps, and primitive normalized models.
Source: Stacks 0941, 06YS, 07A4 and 099N; integral transport in the current blueprint
(blueprint: lem-trf-effective-quotient-model-descent).
Proof:
1. The evaluation calculus makes every reduction normalized. Exact whole-system
   inverse image preserves its transition adjoints by
   lem-pur-system-normalized-tensor-closure and prop-weil-pbc-proetale-constant-exact.
2. lem-pur-coefficient-extension-reduction-model identifies scalar change of that
   same strict reduction diagram with its normalized scalar quotient model. Balanced
   association commutes with every quotient map, even for ramified extensions.
3. Apply lem-pur-normalized-actual-reconstruction-maps to both normalized systems.
   It gives completeness and invertibility of the actual whole-system counits, and
   invertibility of the actual unit for complete inputs, without any bounds.
4. lem-trf-primitive-quotient-realization-comparisons gives the two natural models
   for these very functors and the fixed Roos comparisons. Its normalization tests
   every K-flat presentation, including all strict transitions and tensor generators.
   lem-trf-roos-adjunction-quotient-normalization identifies the counit with the
   K-injective projections and the unit with the zero-shifted quotient augmentation.
   Thus the maps here are the specified adjunction maps, not unrelated isomorphisms. -/
-- STATEMENT-DISPUTED: inherits the universal-presentation normalization obstruction of
-- primitiveQuotientRealizationComparisons; finite derived evaluations do not fix the
-- whole-system presentation isomorphism. See the report and the existing T6 counterexample.
theorem effectiveQuotientModelDescent
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SL : CoefficientDerivedSystemCalculus l L Y)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L Y) :
    (∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l E Y (SY.reduction.obj K) ∧
      IsNormalizedCoefficientSequence l E X
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K)) ∧
      IsNormalizedCoefficientSequence l L Y
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K)) ∧
      IntegralOnSlice.IsComplete l E X none ((coefficientSequenceLimit l E X).obj
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
      IntegralOnSlice.IsComplete l L Y none ((coefficientSequenceLimit l L Y).obj
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) ∧
      IsIso (SX.adjunction.counit.app
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
      IsIso (SL.adjunction.counit.app
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) ∧
      (IntegralOnSlice.IsComplete l E Y none K → IsIso (SY.adjunction.unit.app K))) ∧
    Nonempty (IntegralComparisonPullbackModel l E f SY ρX) ∧
    Nonempty (IntegralComparisonScalarModel l E L ι Y SY ρL) := by
  obtain ⟨hnp, hns⟩ := transportedReductionSystems_normalized l E L ι f _hlX _hlY SY
  obtain ⟨hp, hs⟩ := primitiveQuotientRealizationComparisons l E L ι f Y
    _hlX _hlY _hlY SY SY ρX ρL
  refine ⟨fun K ↦ ?_, hp, hs⟩
  have hx := (purNormalizedReconstructionOfScheme l E X SX).1 _ (hnp K)
  have hl := (purNormalizedReconstructionOfScheme l L Y SL).1 _ (hns K)
  exact ⟨SY.reduction_normalized K, hnp K, hns K, hx.1, hl.1, hx.2, hl.2,
    (purNormalizedReconstructionOfScheme l E Y SY).2 K⟩

/-- Bounded constructibility, with one interval for all reductions, is retained by
both completed operations and their specified system realizations.
Source: Bhatt--Scholze, Lemmas 6.5.4 and 6.5.9(5); current blueprint integral transport
(blueprint: lem-trf-effective-quotient-model-descent).
Proof: apply lem-pur-integral-operations-preserve-constructible(1) to f and K, and
lem-weil-integral-scalar-extension-constructible to E into L and K. Transport through
alpha and beta from lem-trf-primitive-quotient-realization-comparisons. Completeness,
constructible reductions and their common finite interval are invariant under these
isomorphisms. This gives precisely def-weil-derived-complete-integral-detailed for
both realizations, without any bound on the quotient ring map. -/
theorem effectiveQuotientModelConstructible
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L Y)
    (α : IntegralComparisonPullbackModel l E f SY ρX)
    (β : IntegralComparisonScalarModel l E L ι Y SY ρL)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K) ∧
    sfIntegralConstructible l L Y ((integralScalarExtensionOfUniverses l E L ι Y).obj K) ∧
    sfIntegralConstructible l E X ((coefficientSequenceLimit l E X).obj
      ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
    sfIntegralConstructible l L Y ((coefficientSequenceLimit l L Y).obj
      ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) := by
  have hp := ((integralOperations_preserve_constructible l E f).1 K _hK).1
  have hs : sfIntegralConstructible l L Y
      ((integralScalarExtensionOfUniverses l E L ι Y).obj K) :=
    sfIntegralScalarExtension_constructible (l + 1) l (by omega) E L ι Y K _hK
  exact ⟨hp, hs,
    (sfIntegralConstructible l E X).prop_of_iso (α.realization.app K) hp,
    (sfIntegralConstructible l L Y).prop_of_iso (β.realization.app K) hs⟩

section RoosComparisonUniqueness

-- The computes field uses the defining Roos object, so keep this comparison transparent.
attribute [local semireducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted coefficientSequenceLimit
  integralOperationsRoosFunctor integralOperationsGoodLocalization sfIntegralConstructible

private theorem roosComparison_unique (W : Scheme.{t})
    (ρ ρ' : IntegralComparisonRoosModel l E W) : ρ.comparison = ρ'.comparison := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext C
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso q := hq
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).mpr hq
  have : IsIso ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W).map q) := by
    change IsIso ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q))
    infer_instance
  have hi : ρ.comparison.app I = ρ'.comparison.app I := by
    apply Iso.ext
    change ρ.comparison.hom.app I = ρ'.comparison.hom.app I
    exact (ρ.computes I).trans (ρ'.computes I).symm
  apply (cancel_mono ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W).map q)).1
  rw [← ρ.comparison.inv.naturality q, ← ρ'.comparison.inv.naturality q]
  exact congrArg (fun z ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q).map q ≫ z) (congrArg Iso.inv hi)

end RoosComparisonUniqueness

private theorem roosComparison_descent (W : Scheme.{t})
    (ρ₀ : IntegralComparisonRoosModel l E W) :
    ∃ (H : coefficientSequenceRestrictedDerived l E W ⥤
        DerivedCategory (scalarReductionSource l E W))
      (κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ H)
      (ρ : H ≅ coefficientConstantTowerLimit l E W),
      κ.hom ≫ Functor.whiskerLeft DerivedCategory.Q ρ.hom = ρ₀.comparison.inv ∧
      ∀ (ρ' : H ≅ coefficientConstantTowerLimit l E W),
        κ.hom ≫ Functor.whiskerLeft DerivedCategory.Q ρ'.hom = ρ₀.comparison.inv → ρ' = ρ := by
  refine ⟨coefficientConstantTowerLimit l E W, ρ₀.comparison.symm, Iso.refl _, ?_, ?_⟩
  · ext C
    exact Category.comp_id _
  · intro ρ' hρ'
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ))
    intro C
    have h := congrArg (fun k ↦ k.app C) hρ'
    change ρ₀.comparison.inv.app C ≫ ρ'.hom.app (DerivedCategory.Q.obj C) =
      ρ₀.comparison.inv.app C at h
    change ρ'.hom.app (DerivedCategory.Q.obj C) = 𝟙 _
    exact (cancel_epi (ρ₀.comparison.inv.app C)).1
      (h.trans (Category.comp_id _).symm)

/-- Descent respects every representative change and refinement, with the canonical
comparison-preserving uniqueness rather than an arbitrary objectwise isomorphism.
Source: Stacks 06YS, 0G7E and 0941; current blueprint integral transport
(blueprint: lem-trf-effective-quotient-model-descent).
Proof:
1. lem-pur-integral-operations-well-defined(1) and
   lem-weil-integral-scalar-extension-well-defined(1) invert quasi-isomorphisms on
   the two good-complex Roos constructions. Their clauses (2) give the unique
   descended functor comparisons compatible with the representative comparisons.
2. The scalar association is a coherent strict-system map by
   lem-pur-coefficient-extension-reduction-model. The primitive normalization
   composes its inverse with rho. Naturality of each factor proves naturality
   of alpha and beta on every derived map, hence on changes and common refinements.
3. lem-weil-strict-roos-comparison, using exact products from
   lem-weil-proetale-countable-products-exact, computes the same rho on every
   K-injective resolution. Agreement on K-injectives determines the natural
   comparison uniquely. The same representative normalization determines alpha
   and beta uniquely on the localization of all good representatives.
4. The counit is SY.adjunction.counit, a natural transformation on whole systems.
   Its projection formula is the one of
   lem-trf-roos-adjunction-quotient-normalization for every resolution, so changing
   resolutions computes that same morphism before evaluation. -/
theorem effectiveQuotientModelRepresentativeDescent
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L Y)
    (α : IntegralComparisonPullbackModel l E f SY ρX)
    (β : IntegralComparisonScalarModel l E L ι Y SY ρL) :
    (∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (a : P.obj ⟶ Q.obj), QuasiIso a →
      QuasiIso ((integralOperationsPullbackComplexFunctor l E f).map a) ∧
      QuasiIso ((integralScalarComplexFunctor l E L ι Y).map a)) ∧
    (∀ (F : DerivedCategory (scalarReductionSource l E Y) ⥤
        DerivedCategory (scalarReductionSource l E X))
      (c : integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f),
      ∃! a : integralDerivedPullback l E f ≅ F,
        Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) a ≪≫ c =
          integralDerivedPullbackComparison l E f) ∧
    (∀ (F : DerivedCategory (scalarReductionSource l E Y) ⥤
        DerivedCategory (scalarReductionSource l L Y))
      (c : integralOperationsGoodLocalization l E Y ⋙ F ≅ integralScalarOnGood l E L ι Y),
      ∃! a : integralScalarExtensionOfUniverses l E L ι Y ≅ F,
        Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) a ≪≫ c =
          integralScalarExtensionComparisonOfUniverses l E L ι Y) ∧
    (∀ (K K' : DerivedCategory (scalarReductionSource l E Y)) (a : K ⟶ K'),
      (integralDerivedPullback l E f).map a ≫ α.realization.hom.app K' =
        α.realization.hom.app K ≫
          (SY.reduction ⋙ integralComparisonDerivedSequencePullback l E f ⋙
            coefficientSequenceLimit l E X).map a) ∧
    (∀ (K K' : DerivedCategory (scalarReductionSource l E Y)) (a : K ⟶ K'),
      (integralScalarExtensionOfUniverses l E L ι Y).map a ≫ β.realization.hom.app K' =
        β.realization.hom.app K ≫
          (SY.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι Y ⋙
            coefficientSequenceLimit l L Y).map a) ∧
    (∀ α' : IntegralComparisonPullbackModel l E f SY ρX,
      α'.realization = α.realization) ∧
    (∀ β' : IntegralComparisonScalarModel l E L ι Y SY ρL,
      β'.realization = β.realization) ∧
    (∀ ρ' : IntegralComparisonRoosModel l E X, ρ'.comparison = ρX.comparison) ∧
    (∀ ρ' : IntegralComparisonRoosModel l L Y, ρ'.comparison = ρL.comparison) ∧
    (∃ (H : coefficientSequenceRestrictedDerived l E X ⥤
        DerivedCategory (scalarReductionSource l E X))
      (κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ H)
      (ρ : H ≅ coefficientConstantTowerLimit l E X),
      κ.hom ≫ Functor.whiskerLeft DerivedCategory.Q ρ.hom = ρX.comparison.inv ∧
      ∀ (ρ' : H ≅ coefficientConstantTowerLimit l E X),
        κ.hom ≫ Functor.whiskerLeft DerivedCategory.Q ρ'.hom = ρX.comparison.inv → ρ' = ρ) ∧
    (∃ (H : coefficientSequenceRestrictedDerived l L Y ⥤
        DerivedCategory (scalarReductionSource l L Y))
      (κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ H)
      (ρ : H ≅ coefficientConstantTowerLimit l L Y),
      κ.hom ≫ Functor.whiskerLeft DerivedCategory.Q ρ.hom = ρL.comparison.inv ∧
      ∀ (ρ' : H ≅ coefficientConstantTowerLimit l L Y),
        κ.hom ≫ Functor.whiskerLeft DerivedCategory.Q ρ'.hom = ρL.comparison.inv → ρ' = ρ) ∧
    ∀ (N N' : coefficientSequenceDerived l E Y) (a : N ⟶ N'),
      SY.reduction.map ((coefficientSequenceLimit l E Y).map a) ≫
          SY.adjunction.counit.app N' = SY.adjunction.counit.app N ≫ a := by
  have hmodels := primitiveQuotientRealizations_unique l E L ι f SY ρX ρL α β
  refine ⟨?_, ?_, ?_, ?_, ?_, hmodels.1, hmodels.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q a ha
    exact ⟨(integralOperationsWellDefined l E f X).1 P Q a ha,
      ((integralScalarExtensionWellDefined l E L ι Y).1 P Q a ha).2⟩
  · have h := (integralOperationsWellDefined l E f X).2.2.choose_spec.choose_spec
    exact h.choose_spec.choose_spec.1
  · exact (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.2.2.1
  · intro K K' a
    exact α.realization.hom.naturality a
  · intro K K' a
    exact β.realization.hom.naturality a
  · intro ρ'
    exact roosComparison_unique l E X ρ' ρX
  · intro ρ'
    exact roosComparison_unique l L Y ρ' ρL
  · exact roosComparison_descent l E X ρX
  · exact roosComparison_descent l L Y ρL
  · intro N N' a
    exact SY.adjunction.counit.naturality a

universe sa sb sw

section ScalarData
open SheafOfModules
variable {C₀ : Type sa} [Category.{sb} C₀] {J : GrothendieckTopology C₀}
  [J.HasSheafCompose (forget₂ CommRingCat.{sw} RingCat.{sw})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sw}] [HasSheafify J AddCommGrpCat.{sw}]
  [EssentiallySmall.{sw} C₀]

private theorem scalarCompositionData
    {R S T : Sheaf J CommRingCat.{sw}} {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ)
    (A : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (B : SheafOfModules.DerivedChangeOfRingsCochainModel ψ)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel γ) :
    ∃ (c : A.E ⋙ B.E ≅ D.E) (a : A.T ⋙ B.T ≅ D.T),
      (∀ N U z y x, (c.hom.app N).val.app U
        (SheafOfModules.systemModelTmul B (A.E.obj N) U z
          (SheafOfModules.systemModelTmul A N U y x)) =
        SheafOfModules.systemModelTmul D N U (z * ψ.hom.app U y) x) ∧
      ∀ P : CochainComplex
          (ringedSiteModules.{sw} (derivedChangeRingIndependentCoefficients J R)) ℤ,
        B.T.map (A.ε.app P) ≫ B.ε.app ((A.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) =
          a.hom.app (DerivedCategory.Q.obj P) ≫ D.ε.app P := by
  obtain ⟨A', rfl⟩ := SequenceScalarProof.scalarPackageExists φ A
  obtain ⟨B', rfl⟩ := SequenceScalarProof.scalarPackageExists ψ B
  obtain ⟨D', rfl⟩ := SequenceScalarProof.scalarPackageExists γ D
  exact ⟨SheafOfModules.systemScalarModelComposition hγ A' B' D',
    SheafOfModules.systemScalarModelDerivedComposition hγ A' B' D',
    SheafOfModules.systemScalarModelComposition_tmul hγ A' B' D',
    fun P ↦ (SheafOfModules.systemScalarModelDerivedComposition_rep hγ A' B' D' P).symm⟩

private theorem scalarUnitData
    {R : Sheaf J CommRingCat.{sw}} {φ : R ⟶ R} (hφ : φ = 𝟙 R)
    (A : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :
    ∃ (c : A.E ≅ 𝟭 _) (a : A.T ≅ 𝟭 _),
      (∀ N U z x, (c.hom.app N).val.app U
        (SheafOfModules.systemModelTmul A N U z x) = z • x) ∧
      ∀ P : CochainComplex
          (ringedSiteModules.{sw} (derivedChangeRingIndependentCoefficients J R)) ℤ,
        A.ε.app P ≫ DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) =
          a.hom.app (DerivedCategory.Q.obj P) := by
  obtain ⟨A', rfl⟩ := SequenceScalarProof.scalarPackageExists φ A
  exact ⟨SheafOfModules.systemScalarModelUnit hφ A',
    SheafOfModules.systemScalarModelDerivedUnit hφ A',
    SheafOfModules.systemScalarModelUnit_tmul hφ A',
    fun P ↦ (SheafOfModules.systemScalarModelDerivedUnit_rep hφ A' P).symm⟩

end ScalarData

/-- Strict tensor-generator association and unit identities survive localization,
for all coefficient triples, including every equality case.
Source: Stacks 03EK, 06YY and 0941; current blueprint integral transport
(blueprint: lem-trf-effective-quotient-model-descent).
Proof: use the whole-sequence scalar associator of
 def-trf-integral-comparison-sequence-systems, whose generator formula is balanced
multiplication. The primitive quotient association and transition formulas in
lem-trf-primitive-quotient-realization-comparisons send both triple paths to the
same product and give multiplication for the identity inclusion. The universal
cochain counits descend these strict equalities to the displayed derived maps.
Localization and the single Roos functor preserve equality and composition.
The representative-change and resolution independence just stated make these
comparisons simultaneous; no flatness or finite Tor bound is used. -/
theorem effectiveQuotientModelScalarCoherence
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x)) :
    (∃ a : integralComparisonDerivedSequenceScalar l E L ι W ⋙
        integralComparisonDerivedSequenceScalar l L M j W ≅
          integralComparisonDerivedSequenceScalar l E M (j.comp ι) W,
      ∀ C : CochainComplex (coefficientSequenceModules l E W) ℤ,
        (integralComparisonDerivedSequenceScalar l L M j W).map
            ((integralComparisonSequenceScalarModel l E L ι W).ε.app C) ≫
          (integralComparisonSequenceScalarModel l L M j W).ε.app
            (((integralComparisonSequenceScalarModel l E L ι W).E.mapHomologicalComplex
              (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (integralComparisonSequenceScalarComposition l E L ι M j W)
              (.up ℤ)).hom.app C) =
        a.hom.app (DerivedCategory.Q.obj C) ≫
          (integralComparisonSequenceScalarModel l E M (j.comp ι) W).ε.app C) ∧
    (∃ a : integralComparisonDerivedSequenceScalar l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _,
      ∀ C : CochainComplex (coefficientSequenceModules l E W) ℤ,
        (integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) W).ε.app C ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (integralComparisonSequenceScalarUnit l E W) (.up ℤ)).hom.app C) =
        a.hom.app (DerivedCategory.Q.obj C)) := by
  constructor
  · obtain ⟨c, a, hc, ha⟩ := scalarCompositionData
      (sequenceScalarMapComp l E L ι M j W).symm
      (integralComparisonSequenceScalarModel l E L ι W)
      (integralComparisonSequenceScalarModel l L M j W)
      (integralComparisonSequenceScalarModel l E M (j.comp ι) W)
    have hc' : c = integralComparisonSequenceScalarComposition l E L ι M j W := by
      apply (integralComparisonSequenceScalarComposition_existsUnique l E L ι M j W).unique
      · simpa only [sequenceTensorSection_eq] using hc
      · exact (integralComparisonSequenceScalarComposition_existsUnique
          l E L ι M j W).exists.choose_spec
    refine ⟨a, fun C ↦ ?_⟩
    simpa only [hc', integralComparisonDerivedSequenceScalar] using ha C
  · obtain ⟨c, a, hc, ha⟩ := scalarUnitData (sequenceScalarMapId l E W)
      (integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) W)
    have hc' : c = integralComparisonSequenceScalarUnit l E W := by
      apply (integralComparisonSequenceScalarUnit_existsUnique l E W).unique
      · simpa only [sequenceTensorSection_eq] using hc
      · exact (integralComparisonSequenceScalarUnit_existsUnique l E W).exists.choose_spec
    refine ⟨a, fun C ↦ ?_⟩
    simpa only [hc', integralComparisonDerivedSequenceScalar] using ha C


/-- The normalized models can be chosen simultaneously over every field, scheme,
map and inclusion in the fixed universe bound, retaining all quotient transitions.
Source: current blueprint integral transport; Stacks 06YS, 06YY and 0941
(blueprint: lem-trf-effective-quotient-model-descent).
Proof: choose the evaluation calculus for every field and scheme by
lem-coef-derived-system-evaluation-calculus and its normalized Roos construction
by lem-trf-roos-adjunction-quotient-normalization. Choose the primitive pullback
and scalar models of lem-trf-primitive-quotient-realization-comparisons for those
same choices. The preceding representative-descent assertion makes their
comparisons independent of all representatives and common refinements. The
strict generator transition, triple association and identity equations survive
localization as in effectiveQuotientModelScalarCoherence. Thus these simultaneous
choices retain exactly the prescribed model normalization. The ambient effectivity
assertion and the constructibility assertion apply to each choice. -/
-- STATEMENT-DISPUTED: inherits the universal-presentation normalization obstruction of
-- primitiveQuotientRealizationComparisons; finite derived evaluations do not fix the
-- whole-system presentation isomorphism. See the report and the existing T6 counterexample.
theorem effectiveQuotientModelsSimultaneous (q : ℕ) [Fact q.Prime] :
    ∃ (S : ∀ (F : Type u) [Field F] [Algebra ℚ_[q] F]
        [FiniteDimensional ℚ_[q] F] (W : Scheme.{u})
        [∀ x : W, Invertible (q : W.residueField x)], CoefficientDerivedSystemCalculus q F W)
      (ρ : ∀ (F : Type u) [Field F] [Algebra ℚ_[q] F]
        [FiniteDimensional ℚ_[q] F] (W : Scheme.{u})
        [∀ x : W, Invertible (q : W.residueField x)], IntegralComparisonRoosModel q F W),
      (∀ (F : Type u) [Field F] [Algebra ℚ_[q] F] [FiniteDimensional ℚ_[q] F]
        (X Y : Scheme.{u}) [∀ x : X, Invertible (q : X.residueField x)]
        [∀ y : Y, Invertible (q : Y.residueField y)] (f : X ⟶ Y),
        Nonempty (IntegralComparisonPullbackModel q F f (S F Y) (ρ F X))) ∧
      (∀ (F : Type u) [Field F] [Algebra ℚ_[q] F] [FiniteDimensional ℚ_[q] F]
        (G : Type u) [Field G] [Algebra ℚ_[q] G] [FiniteDimensional ℚ_[q] G]
        (i : F →ₐ[ℚ_[q]] G) (W : Scheme.{u})
        [∀ x : W, Invertible (q : W.residueField x)],
        Nonempty (IntegralComparisonScalarModel q F G i W (S F W) (ρ G W))) := by
  classical
  have models (F : Type u) [Field F] [Algebra ℚ_[q] F]
      [FiniteDimensional ℚ_[q] F] (W : Scheme.{u})
      [∀ x : W, Invertible (q : W.residueField x)] :
      ∃ S : CoefficientDerivedSystemCalculus q F W,
        Nonempty (IntegralComparisonRoosModel q F W) := by
    obtain ⟨S, _, M, D, _⟩ := roosAdjunctionQuotientNormalization q F W
    exact ⟨S, ⟨roosModel q F W S M D⟩⟩
  let S := fun (F : Type u) [Field F] [Algebra ℚ_[q] F]
    [FiniteDimensional ℚ_[q] F] (W : Scheme.{u})
    [∀ x : W, Invertible (q : W.residueField x)] ↦ (models F W).choose
  let ρ := fun (F : Type u) [Field F] [Algebra ℚ_[q] F]
    [FiniteDimensional ℚ_[q] F] (W : Scheme.{u})
    [∀ x : W, Invertible (q : W.residueField x)] ↦
      (models F W).choose_spec.some
  refine ⟨S, ρ, ?_, ?_⟩
  · intro F _ _ _ X Y _ _ f
    exact (primitiveQuotientRealizationComparisons q F F (AlgHom.id ℚ_[q] F) f Y
      (fun x ↦ isUnit_of_invertible _) (fun y ↦ isUnit_of_invertible _)
      (fun y ↦ isUnit_of_invertible _) (S F Y) (S F Y) (ρ F X) (ρ F Y)).1
  · intro F _ _ _ G _ _ _ i W _
    exact (primitiveQuotientRealizationComparisons q F G i (𝟙 W) W
      (fun x ↦ isUnit_of_invertible _) (fun x ↦ isUnit_of_invertible _)
      (fun x ↦ isUnit_of_invertible _) (S F W) (S F W) (ρ F W) (ρ G W)).2

end WeilConjectures
