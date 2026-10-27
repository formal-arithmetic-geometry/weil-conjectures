/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.IntegralSupportFunctorNormalization
public import Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent

/-! # Open compact support through the coefficient stages

Source: latest blueprint, lem-zl-morphism-open-closed-reduction, Part 2;
Stacks Tags 03DJ, 0GL1, 0E8I and 010N; Bhatt--Scholze 6.8.14
(blueprint: lem-zl-open-extension-texact-coefficient-stages).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlOpenTExact
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients
open IntegralSupportNormalization
open CoefficientStageDescent

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [U.Over (Spec (.of D.k))] [baseX : X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [sepU : IsSeparated (U ↘ Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [j.IsOver (Spec (.of D.k))]

set_option linter.unusedSectionVars false in
include baseX ftX qcX in
/-- The open immersion is quasi-compact because X is Noetherian.
Source: latest blueprint Part 2; finite-type schemes over fields are Noetherian
(blueprint: lem-zl-open-extension-texact-coefficient-stages).
Proof: finite type over the field makes X Noetherian. Every open in a Noetherian
space is quasi-compact, so the open immersion j is quasi-compact. -/
theorem quasiCompact : QuasiCompact j := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  infer_instance

section Compact
variable [QuasiCompact j]

/-- The actual integral operation for the compactification (j,id).
Source: blueprint Part 2 (blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
abbrev integral (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  sfCompactSupportFiniteIntegralFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion j) E

/-- Its specified rational Hom action, with no completion of the rational category.
Source: blueprint Part 2 (blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
abbrev rational (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion j) E

/-- The canonical integral identification: fixed Roos realization, then the proper identity.
Source: blueprint Part 2 (blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
def identification (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    integral D l hl j E ⋙ (sfIntegralConstructible l E X).ι ≅
      (sfIntegralConstructible l E U).ι ⋙ ordinaryOpen l E j :=
  (sfQcqsCompactSupportRealization l E D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
      (Compactification.ofIsOpenImmersion j)).symm ≪≫
    isoWhiskerLeft (sfIntegralConstructible l E U).ι (openIdentity l E j)

/-- The cohomology map is H^a(d), followed by the exact-functor cycles/quotient map.
Source: Stacks 010N (blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
def integralCohomology (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (a : ℤ) :
    integral D l hl j E ⋙ (sfIntegralConstructible l E X).ι ⋙
        DerivedCategory.homologyFunctor (scalarReductionSource l E X) a ≅
      (sfIntegralConstructible l E U).ι ⋙
        DerivedCategory.homologyFunctor (scalarReductionSource l E U) a ⋙
          PurCompactSupport.openExtension (PurCompactSupport.completed.{u} l E) j :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (identification D l hl j E) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (sfIntegralConstructible l E U).ι
      (Functor.mapDerivedCategoryHomologyFunctorIso
        (PurCompactSupport.openExtension (PurCompactSupport.completed.{u} l E) j) a).symm



/-- The universal scalar model, normalized on every complex by its K-flat counit.
The equality of ordinary functors records the same sectionwise tensor construction.
Source: Stacks 06YY; Bhatt--Scholze 6.8.2
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
structure ScalarModel (E L : Type u) [Field E] [Field L]
    [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
    (i : E →ₐ[ℚ_[l]] L) (T : Scheme.{u}) where
  ordinary : pbcExtend (completedCoefficientMap l E L i T) = integralOrdinaryScalar l E L i T
  complex : (pbcExtend (completedCoefficientMap l E L i T)).mapHomologicalComplex (.up ℤ) =
    (integralOrdinaryScalar l E L i T).mapHomologicalComplex (.up ℤ)
  comparison : pbcDerivedExtend (completedCoefficientMap l E L i T) ≅
    integralOrdinaryDerivedScalar l E L i T
  counit : ∀ P : CochainComplex (integralTowerModules l E T) ℤ,
    comparison.hom.app (DerivedCategory.Q.obj P) ≫
        (integralOrdinaryScalar l E L i T).mapDerivedCategoryFactors.hom.app P =
      pbcComplexCounit (completedCoefficientMap l E L i T) P ≫
        DerivedCategory.Q.map (eqToHom (congrArg
          (fun F ↦ F.obj P) complex))

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The canonical scalar realization: the universal scalar counit followed by the
existing quotient/Roos-normalized ordinary-to-completed comparison, in reverse.
Source: blueprint Part 2 (blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
def scalarRealization (T : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L)
    (M : ScalarModel l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) T) :
    integralTransition l Ω T E L h ⋙ (sfIntegralConstructible l
        (Coefficient.{u} l Ω L) T).ι ≅
      (sfIntegralConstructible l (Coefficient.{u} l Ω E) T).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) T) :=
  (sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) T).symm ≪≫
      isoWhiskerLeft (sfIntegralConstructible l (Coefficient.{u} l Ω E) T).ι M.comparison.symm


/-- The inherited additive shifts, bundled as a family to avoid Pi-instance search.
Source: Mathlib full-subcategory shifts
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
instance integralShiftAdditive (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l E T) n).Additive :=
  fun n ↦ ObjectProperty.instAdditiveFullSubcategoryShiftFunctor (sfIntegralConstructible l E T) n

/-- The recorded stage-transition shift, exposed at the stage-system interface.
Source: blueprint coefficient stages
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
instance scalarShift (T : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L) :
    ((stageSystem l Ω T).T h).CommShift ℤ :=
  stageTransitionCommShift l Ω T E L h

/-- The recorded inclusion shift, exposed at the stage-system interface.
Source: blueprint coefficient stages
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
instance stageInclusionShift (T : Scheme.{u}) (E : Index l Ω) :
    ((stageSystem l Ω T).ι E).CommShift ℤ :=
  inclusionCommShift E

/-- The canonical shift comparison of exact ordinary open extension.
Source: Mathlib's exact derived functor construction
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
instance ordinaryOpenShift (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] : (ordinaryOpen l E j).CommShift ℤ :=
  inferInstance

attribute [local irreducible] ordinaryOpenShift

attribute [local irreducible] sfIntegralConstructible
  sfRationalStandardTStructure sfCommonStageStandardTStructure
  identification scalarRealization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The specified pullback mate and ordinary adjunction equations, together with both
strict-system realization equations. The mate uses the fixed identification and the
strict-realized counit, rather than an independently chosen comparison.
Source: blueprint Part 2; IntegralSupportNormalization.Normalization.openSystemUnit
and openSystemCounit (blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
def OpenAdjunctionNormalization (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)] : Prop :=
  ∃ (openPull : constructibleIntegralPullback l E j ⋙
        (sfIntegralConstructible l E U).ι ≅
      (sfIntegralConstructible l E X).ι ⋙
        ordinaryOpenPull l E j),
  ∃ (adjunction : integral D l hl j E ⊣
      constructibleIntegralPullback l E j),
  (∀ (K : sfIntegralConstructibleCategory l E U),
    (adjunction.unit.app K).hom ≫ openPull.hom.app
        ((integral D l hl j E).obj K) =
      (ordinaryOpenAdjunction l E j).unit.app K.obj ≫
        (ordinaryOpenPull l E j).map
          ((identification D l hl j E).inv.app K)) ∧
  (∀ (K : sfIntegralConstructibleCategory l E X),
    (adjunction.counit.app K).hom =
      (identification D l hl j E).hom.app
          ((constructibleIntegralPullback l E j).obj K) ≫
        (ordinaryOpen l E j).map (openPull.hom.app K) ≫
          (ordinaryOpenAdjunction l E j).counit.app K.obj) ∧
  (∀ (K : sfIntegralConstructibleCategory l E X),
    openPull.hom.app K =
      (ordinaryOpenAdjunction l E j).unit.app
          ((constructibleIntegralPullback l E j).obj K).obj ≫
        (ordinaryOpenPull l E j).map
          ((identification D l hl j E).inv.app
            ((constructibleIntegralPullback l E j).obj K)) ≫
        (ordinaryOpenPull l E j).map
          ((adjunction.counit.app K).hom)) ∧
  (∀ (N : sfIntegralConstructibleCategory l E U),
    (FrobeniusExchange.reduction l E U).map (adjunction.unit.app N).hom ≫
      (integralComparisonPullbackCounit l E j
        ((FrobeniusExchange.models l E).system X)
        ((FrobeniusExchange.models l E).system U)
        ((FrobeniusExchange.models l E).roos U)
        ((FrobeniusExchange.models l E).pullback j)).app
          (((integral D l hl j E).obj N).obj) ≫
      (integralComparisonDerivedSequencePullback l E j).map
        ((FrobeniusExchange.compactOperationReduction l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j
          (Compactification.ofIsOpenImmersion j)).app N ≫
          (systemDirectId l E X).hom.app
            ((FrobeniusExchange.systemDerivedOpen l E j).obj
              ((FrobeniusExchange.reduction l E U).obj N.obj))) =
    (FrobeniusExchange.systemDerivedOpenAdjunction l E j).unit.app
      ((FrobeniusExchange.reduction l E U).obj N.obj)) ∧
  (∀ (K : sfIntegralConstructibleCategory l E X),
    (FrobeniusExchange.reduction l E X).map (adjunction.counit.app K).hom =
      ((FrobeniusExchange.compactOperationReduction l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) j
        (Compactification.ofIsOpenImmersion j)).app
          ((constructibleIntegralPullback l E j).obj K)) ≫
      (systemDirectId l E X).hom.app
        ((FrobeniusExchange.systemDerivedOpen l E j).obj
          ((FrobeniusExchange.reduction l E U).obj
            ((constructibleIntegralPullback l E j).obj K).obj)) ≫
      (FrobeniusExchange.systemDerivedOpen l E j).map
        ((integralComparisonPullbackCounit l E j
          ((FrobeniusExchange.models l E).system X)
          ((FrobeniusExchange.models l E).system U)
          ((FrobeniusExchange.models l E).roos U)
          ((FrobeniusExchange.models l E).pullback j)).app K.obj) ≫
      (FrobeniusExchange.systemDerivedOpenAdjunction l E j).counit.app
        ((FrobeniusExchange.reduction l E X).obj K.obj))

attribute [local irreducible] OpenAdjunctionNormalization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The standard rational t-structure on the named coefficient stage.
The named stage carries the same category and shift structures as its rational model.
Source: blueprint Part 2; the standard coefficient stages
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
def stageStandardTStructure (T : Scheme.{u})
    [T.Over (Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))] (E : Index l Ω) :
    Triangulated.TStructure (GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  sfRationalStandardTStructure l (Coefficient.{u} l Ω E) T D hl

attribute [local irreducible] stageStandardTStructure

set_option linter.unusedSectionVars false in
/-- All comparisons refer to the supplied normalized coefficient action, whose finite
functors, mixed tensor units, strict quotient transitions and Roos projections are fixed.
The t-structures are specified by the recorded standard classes; every comparison is
normalized by its truncation unit and counit via CoefficientStageDescent.Comparisons.
Source: latest blueprint Part 2; Stacks 0GL1; Bhatt--Scholze 6.8.14
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
def AllStages
    (S : SfCompactSupportCoefficientAction l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) Ω
      (Compactification.ofIsOpenImmersion j)) : Prop :=
  ∃ (invertibleU : ∀ x : U, Invertible (l : U.residueField x)),
  letI := invertibleU;
  ∃ (invertibleX : ∀ x : X, Invertible (l : X.residueField x)),
  letI := invertibleX;
  ∃ (tU : ∀ E : Index l Ω,
    Triangulated.TStructure (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U)),
  ∃ (tX : ∀ E : Index l Ω,
    Triangulated.TStructure (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)),
  (∀ E : Index l Ω, (tU E).bounded = ⊤) ∧
  (∀ E : Index l Ω, (tX E).bounded = ⊤) ∧
  (∀ (E : Index l Ω) (n : ℤ),
    (tU E).le n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) U true n ∧
    (tU E).ge n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) U false n) ∧
  (∀ (E : Index l Ω) (n : ℤ),
    (tX E).le n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) X true n ∧
    (tX E).ge n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) X false n) ∧
  ∃ (integralShift : ∀ E : Index l Ω, (integral D l hl j (Coefficient.{u} l Ω E)).CommShift ℤ),
  letI := integralShift;
  ∃ (rationalShift : ∀ E : Index l Ω, (S.system.Φ E).CommShift ℤ),
  letI := rationalShift;
  ∃ (commonShift : S.system.functor.CommShift ℤ),
  letI := commonShift;
  ∃ (scalarShiftU : ∀ (E L : Index l Ω) (h : E ≤ L),
    ((stageSystem l Ω U).T h).CommShift ℤ),
  letI := scalarShiftU;
  ∃ (scalarShiftX : ∀ (E L : Index l Ω) (h : E ≤ L),
    ((stageSystem l Ω X).T h).CommShift ℤ),
  letI := scalarShiftX;
  ∃ (inclusionShiftU : ∀ E : Index l Ω, ((stageSystem l Ω U).ι E).CommShift ℤ),
  letI := inclusionShiftU;
  ∃ (inclusionShiftX : ∀ E : Index l Ω, ((stageSystem l Ω X).ι E).CommShift ℤ),
  letI := inclusionShiftX;
  (∀ (E L : Index l Ω) (h : E ≤ L),
    scalarShiftU E L h = scalarShift l Ω U E L h ∧
    scalarShiftX E L h = scalarShift l Ω X E L h) ∧
  (∀ E : Index l Ω,
    inclusionShiftU E = stageInclusionShift l Ω U E ∧
    inclusionShiftX E = stageInclusionShift l Ω X E) ∧
  ∃ (integralComparisons : ∀ E : Index l Ω,
    Comparisons (tU E) (tX E) (integral D l hl j (Coefficient.{u} l Ω E))),
  ∃ (rationalComparisons : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω U E)
      (stageStandardTStructure D l hl Ω X E)
      (S.system.Φ E) (rationalShift E)),
  ∃ (commonComparisons :
    Comparisons (sfCommonStageStandardTStructure l U Ω D hl)
      (sfCommonStageStandardTStructure l X Ω D hl) S.system.functor),
  ∃ (ambientU : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (tU E) DerivedCategory.TStructure.t
      (sfIntegralConstructible l (Coefficient.{u} l Ω E) U).ι
      (ObjectProperty.commShiftι _ (A := ℤ))),
  ∃ (ambientX : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (tX E) DerivedCategory.TStructure.t
      (sfIntegralConstructible l (Coefficient.{u} l Ω E) X).ι
      (ObjectProperty.commShiftι _ (A := ℤ))),
  ∃ (ordinary : ∀ E : Index l Ω,
    @Comparisons _ _ _ _ _ (fun _n ↦ inferInstance) _
      _ _ _ _ _ (fun _n ↦ inferInstance) _
      DerivedCategory.TStructure.t DerivedCategory.TStructure.t
      (ordinaryOpen l (Coefficient.{u} l Ω E) j)
      (ordinaryOpenShift l j (Coefficient.{u} l Ω E))),
  (∀ E : Index l Ω,
    @SquareCompatible
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (DerivedCategory (scalarReductionSource l (Coefficient.{u} l Ω E) U))
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (DerivedCategory (scalarReductionSource l (Coefficient.{u} l Ω E) X))
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _ _
      _ (integralShift E)
      (ordinaryOpen l (Coefficient.{u} l Ω E) j) (ordinaryOpenShift l j (Coefficient.{u} l Ω E))
      _ (ObjectProperty.commShiftι _ (A := ℤ))
      _ (ObjectProperty.commShiftι _ (A := ℤ))
      (integralComparisons E) (ordinary E) (ambientU E) (ambientX E)
      (identification D l hl j (Coefficient.{u} l Ω E))) ∧
  (∀ E : Index l Ω,
    PreservesFiniteLimits (PurCompactSupport.openExtension
      (PurCompactSupport.completed.{u} l (Coefficient.{u} l Ω E)) j) ∧
    PreservesFiniteColimits (PurCompactSupport.openExtension
      (PurCompactSupport.completed.{u} l (Coefficient.{u} l Ω E)) j)) ∧
  (∀ (E : Index l Ω) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    IsSfDerivedComplete l (Coefficient.{u} l Ω E) X
      ((ordinaryOpen l (Coefficient.{u} l Ω E) j).obj K.obj)) ∧
  (∀ (E : Index l Ω)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    sfIntegralConstructible l (Coefficient.{u} l Ω E) X
      ((ordinaryOpen l (Coefficient.{u} l Ω E) j).obj K.obj)) ∧
  (∀ (E : Index l Ω) (b : Bool) (n : ℤ)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    sfIntegralStandardClass l (Coefficient.{u} l Ω E) U b n K →
      sfIntegralStandardClass l (Coefficient.{u} l Ω E) X b n
        ((integral D l hl j (Coefficient.{u} l Ω E)).obj K)) ∧
  (∀ E : Index l Ω, OpenAdjunctionNormalization D l hl j (Coefficient.{u} l Ω E)) ∧
  ∃ (localizationU : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (tU E) (stageStandardTStructure D l hl Ω U E)
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) U)
      (sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) U)),
  ∃ (localizationX : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (tX E) (stageStandardTStructure D l hl Ω X E)
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X)
      (sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) X)),
  ∃ (rationalization : ∀ E : Index l Ω,
    sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) U ⋙ S.system.Φ E ≅
      integral D l hl j (Coefficient.{u} l Ω E) ⋙
        sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X),
  (∀ (E : Index l Ω)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    HEq ((rationalization E).hom.app K)
      (𝟙 ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        ((integral D l hl j (Coefficient.{u} l Ω E)).obj K)))) ∧
  (∀ E : Index l Ω,
    @SquareCompatible
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _ _
      _ (sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) U)
      _ (sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) X)
      _ (integralShift E) _ (rationalShift E)
      (localizationU E) (localizationX E)
      (integralComparisons E) (rationalComparisons E) (rationalization E)) ∧
  ∃ (integralScalarU : ∀ (E L : Index l Ω) (h : E ≤ L),
    Comparisons (tU E) (tU L) (integralTransition l Ω U E L h)),
  ∃ (integralScalarX : ∀ (E L : Index l Ω) (h : E ≤ L),
    Comparisons (tX E) (tX L) (integralTransition l Ω X E L h)),
  (∀ (E L : Index l Ω) (h : E ≤ L),
    SquareCompatible (integralComparisons E) (integralComparisons L)
      (integralScalarU E L h) (integralScalarX E L h) (S.integralBeta h)) ∧
  ∃ (scalarModelU : ∀ (E L : Index l Ω) (h : E ≤ L),
    ScalarModel l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) U),
  ∃ (scalarModelX : ∀ (E L : Index l Ω) (h : E ≤ L),
    ScalarModel l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) X),
  (∀ (E L : Index l Ω) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    ((S.integralBeta h).hom.app K).hom ≫
        (identification D l hl j (Coefficient.{u} l Ω L)).hom.app
          ((integralTransition l Ω U E L h).obj K) ≫
        (ordinaryOpen l (Coefficient.{u} l Ω L) j).map
          ((scalarRealization l Ω U E L h (scalarModelU E L h)).hom.app K) =
      (scalarRealization l Ω X E L h (scalarModelX E L h)).hom.app
          ((integral D l hl j (Coefficient.{u} l Ω E)).obj K) ≫
        (pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X)).map
            ((identification D l hl j (Coefficient.{u} l Ω E)).hom.app K) ≫
        (PurCompactSupport.openComparison (PurCompactSupport.completedChange l
          (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h)) j).app K.obj) ∧
  ∃ (scalarU : ∀ (E L : Index l Ω) (h : E ≤ L),
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω U E)
      (stageStandardTStructure D l hl Ω U L)
      ((stageSystem l Ω U).T h) (scalarShiftU E L h)),
  ∃ (scalarX : ∀ (E L : Index l Ω) (h : E ≤ L),
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω X E)
      (stageStandardTStructure D l hl Ω X L)
      ((stageSystem l Ω X).T h) (scalarShiftX E L h)),
  (∀ (E L : Index l Ω) (h : E ≤ L),
    @SquareCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _ _
      _ (rationalShift E) _ (rationalShift L) _ (scalarShiftU E L h) _ (scalarShiftX E L h)
      (rationalComparisons E) (rationalComparisons L)
      (scalarU E L h) (scalarX E L h) (S.system.β h)) ∧
  ∃ (inclusionU : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω U E)
      (sfCommonStageStandardTStructure l U Ω D hl)
      ((stageSystem l Ω U).ι E) (inclusionShiftU E)),
  ∃ (inclusionX : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω X E)
      (sfCommonStageStandardTStructure l X Ω D hl)
      ((stageSystem l Ω X).ι E) (inclusionShiftX E)),
  (∀ E : Index l Ω,
    @SquareCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (generalAlgebraicallyClosedConstructibleCategory l Ω U)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (generalAlgebraicallyClosedConstructibleCategory l Ω X)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _ _
      _ (inclusionShiftU E) _ (inclusionShiftX E) _ (rationalShift E) _ _
      (inclusionU E) (inclusionX E) (rationalComparisons E)
      commonComparisons (S.system.ιCompFunctorIso E)) ∧
  (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
    @CompositeCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U M)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _
      _ (scalarShiftU E L h) _ (scalarShiftU L M k) _ (scalarShiftU E M (h.trans k))
      (scalarU E L h) (scalarU L M k) (scalarU E M (h.trans k))
      ((stageSystem l Ω U).assoc h k) ∧
    @CompositeCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X M)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _
      _ (scalarShiftX E L h) _ (scalarShiftX L M k) _ (scalarShiftX E M (h.trans k))
      (scalarX E L h) (scalarX L M k) (scalarX E M (h.trans k))
      ((stageSystem l Ω X).assoc h k)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    @CompositeCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (generalAlgebraicallyClosedConstructibleCategory l Ω U)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _
      _ (scalarShiftU E L h) _ (inclusionShiftU L) _ (inclusionShiftU E)
      (scalarU E L h) (inclusionU L) (inclusionU E)
      ((stageSystem l Ω U).transIso h) ∧
    @CompositeCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (generalAlgebraicallyClosedConstructibleCategory l Ω X)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _
      _ (scalarShiftX E L h) _ (inclusionShiftX L) _ (inclusionShiftX E)
      (scalarX E L h) (inclusionX L) (inclusionX E)
      ((stageSystem l Ω X).transIso h)) ∧
  True

attribute [local irreducible] SfCompactSupportCoefficientAction.representative
  SfCompactSupportCoefficientAction.comparison

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 800000 in
-- The representative type carries both source and target finite-stage proofs.
/-- Independence refers to the specified beta-conjugated arrow representatives and
comparison isomorphisms, with respect to the specified presentations of each object.
Source: blueprint Part 2; finite-field independence
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
def RepresentativeIndependence
    (S : SfCompactSupportCoefficientAction l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) Ω
      (Compactification.ofIsOpenImmersion j)) : Prop :=
  (∀ (A P : Pair l Ω U) (α : A ≅ P),
         S.comparison α α = Iso.refl (S.value A)) ∧
       (∀ (A B C P : Pair l Ω U) (α : A ≅ P) (β : B ≅ P) (γ : C ≅ P),
         S.comparison α β ≪≫ S.comparison β γ = S.comparison α γ) ∧
       (∀ (A B : Pair l Ω U) (M N : Index l Ω)
         (hAM : A.stage ≤ M) (hBM : B.stage ≤ M)
         (hAN : A.stage ≤ N) (hBN : B.stage ≤ N)
         (uM : StageHom A B ⟨M, hAM, hBM⟩) (uN : StageHom A B ⟨N, hAN, hBN⟩),
         ofHom A B M hAM hBM uM = ofHom A B N hAN hBN uN →
           S.representative A B M hAM hBM uM = S.representative A B N hAN hBN uN) ∧
       (∀ (A B P : Pair l Ω U) (α : A ≅ P) (β : B ≅ P)
         (M : Index l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
         (f : StageHom A B ⟨M, hA, hB⟩),
         ofHom A B M hA hB f = α.hom ≫ β.inv →
           (S.comparison α β).hom = S.representative A B M hA hB f)
attribute [local irreducible] AllStages RepresentativeIndependence

end Compact

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

set_option maxHeartbeats 800000 in
-- The coefficient-action type has several dependent stage-system parameters.
set_option linter.unusedSectionVars false in
include sepU sepX in
/-- Open compact support is exact through the integral, rational and common stages.
All data in AllStages are conclusions, including both scalar-model normalizations;
there is no t-exactness, completeness, finite-Tor or quasi-compactness input.
Source: latest blueprint, lem-zl-morphism-open-closed-reduction, Part 2;
Stacks 03DJ, 0GL1, 0E8I, 09BP, 010N; Bhatt--Scholze 6.8.11 and 6.8.14
(blueprint: lem-zl-open-extension-texact-coefficient-stages).
Proof:
1. Apply lem-sf-open-roos-extension-comparison to j: U and X are Noetherian and qcqs and j is
quasi-compact. Apply lem-kun-dimension-finite-type separately to U and X to get finite
dimension. Their local rings are k-algebras, so ell is invertible. The category here is the
intrinsic category of def-weil-derived-complete-integral-detailed. For that very category,
lem-sf-intrinsic-integral-standard-truncations gives ambient boundedness and closure under both
ambient truncations, without assuming compatible etale-origin witnesses. It is a full
triangulated subcategory by lem-weil-integral-constructible-triangulated. Ambient orthogonality
restricts to this full subcategory, its truncation triangles stay inside, and its objects are
bounded; thus its standard pair is a bounded t-structure with the ambient truncations and maps.
At rational and common stages prop-constructible-truncations supplies the bounded standard
t-structures and finite-stage truncation maps. By def-weil-constructible-standard-tstructure the
rational halves are the isomorphism closures of integral halves; hence raw localization is
t-exact directly from these definitions. These are the categories and pairs required below, for
every finite enlargement of E.

2. Write R for the completed integral coefficient sheaf and let Rcal and Lcal denote reduction
and total derived limit. For the chosen compactification (j,id_X), the proper-image factor is
the identity. Thus the actual functor in def-weil-integral-rational-qbar-compact-support is
Lcal_X J_j Rcal_U, with precisely the strict quotient transitions specified there. Apply
lem-sf-integral-open-reduction-comparison to the complete K. It gives a whole-system isomorphism
r_j(K):Rcal_X(j_!K) ≅ J_j Rcal_U K, invertibility of the actual unit u_{j_!K}, and the natural
comparison
 d_K = u_{j_!K}^{-1} Lcal_X(r_j(K))^{-1}: J_{O_E}K ≅ j_!K.
Its evaluations are the canonical open tensor maps, with all quotient transitions retained. The
same cited statement identifies the realized unit and counit with the localized ringed-site unit
and counit. In particular this identifies the actual functor and adjunction, rather than
choosing an isomorphic object separately for each K.

3. The same integral comparison states that j_!K is derived complete. For constructibility apply
lem-sf-integral-compact-support-constructible with f=j and c=(j,id_X): j is separated and of
finite type, its source and target are finite type over k, and ell is invertible. The strict
tower in that lemma is exactly the tower of Step 2, so J_{O_E}K belongs to D^b_c(X,O_E), and its
isomorphism d_K puts j_!K in that full subcategory as well. This obtains both finite-level
constructibility and one uniform reduction interval; it imposes no finite-Tor condition over
A_{E,n}. Finally, lem-pur-site-restriction-module-adjunction-exact applied to the completed
ringed slice says that the underlying module-sheaf extension by zero is exact.

4. Represent K by a cochain complex C of completed-ring modules. By
lem-sp-exact-functor-preserves-homology(c), exact j_! identifies the cycles, boundaries and
quotient in degree a, naturally in C:
 H^a(j_!C) = ker(j_!d^a)/im(j_!d^{a-1}) ≅ j_!(ker d^a/im d^{a-1}) = j_!H^a(C).
Consequently it preserves quasi-isomorphisms. Its termwise action is additive, commutes with
shifts and with the signed mapping-cone formula, and hence induces an exact triangulated
integral functor with its usual shift comparison. Compose the displayed cohomology isomorphism
with H^a(d_K). This gives the claimed canonical H^a(J_{O_E}K) ≅ j_!H^a(K) and preserves either
vanishing half-line, for any a. These are ambient cohomology sheaves of complete objects. No
assertion that H^a(K tensor^L A_{E,n}) equals a reduction of H^a(K) enters the argument.

5. For E contained in L write T for the actual completed scalar extension. By
lem-pod-completed-scalar-extension-texact, T is the derived functor of exact ordinary
coefficient extension, equals its defining strict-limit construction, and preserves both
integral halves. The arbitrary-ring open tensor comparison of lem-sf-open-tensor-normalization
gives gamma:T_X j_{E!} ≅ j_{L!} T_U. This comparison includes the open unit: after restriction
it is the identity. Its compatibility with the actual completed construction is also explicit:
at quotient m its generator map is [x] tensor b ↦ [x tensor b|_U]; quotient maps send b to its
image, so these maps form one strict tower map. Apply the augmentation-normalized lambda of
lem-sf-open-roos-extension-comparison over O_L to pass through the defining derived limit of
def-weil-integral-scalar-extension. It preserves the scalar-unit augmentation, so the resulting
gamma is the completed open tensor comparison with the same unit. Under d_E and d_L the
compact-support scalar map is
 b_{L/E}=d_L^{-1} gamma T_X(d_E).
This is the prescribed map of def-weil-compact-support-coefficient-action: its mixed unit has
exactly s tensor x ↦ iota_m(s) tensor (1 tensor x), followed by the same limit map. The
coherence assertion of lem-fix-operation-reduction ensures these comparisons preserve tensor
associators, units and counits, and successive scalar extensions, as actual derived maps. This
uses a simultaneous strict construction, not faithfulness of separate reduction functors.

6. Apply lem-a1-texact-coefficient-stage-descent to the integral functors of Step 4 for all
finite E. They are O_E-linear because termwise j_! and d_E preserve scalar multiplication. The
integral and rational bounded t-structures, the t-exact localization and the finite-stage
truncations were checked in Step 1. The exact t-exact scalar transitions are given by
lem-pod-completed-scalar-extension-texact, rationalized; the compatible beta maps are the b maps
of Step 5, rationalized. The raw localization and pair categories are exactly
def-weil-rationalization-karoubi and def-weil-algebraically-closed-coefficients. In particular
triangles are images of integral triangles up to isomorphism, or represented over one finite
field, as required by the descent lemma. Its descended functors are the actual J_E and J_Qlb of
def-weil-integral-rational-qbar-compact-support, since that definition uses the same integral
values and scalar action. The descent lemma now gives preservation of both standard halves,
exact functors of hearts, and canonical natural cohomology comparisons. Invert its F H^a ≅ H^a F
comparison to obtain the direction H^a(J_Lambda L) ≅ J_Lambda H^a(L) requested here.

7. The integral comparison of Step 4 is the canonical truncation comparison: its kernel and
quotient maps are exactly the cycle inclusion and homology projection. Uniqueness in
lem-pod-texact-truncation-comparison therefore identifies it with the cohomology comparison used
in Step 6 after localization. That lemma also says its truncation comparisons commute with
natural transformations and composition. Apply this to d_E, to t-exact rationalization, and to
b_{L/E} between the two composites of t-exact functors of Step 5, then shift by a. It follows
that the integral, rational and common-stage cohomology maps commute with the specified scalar
comparisons. The open unit already matches the ringed-site unit by Step 2, and its scalar
normalization was checked in Step 5. Finally lem-a1-texact-coefficient-stage-descent states that
the common-stage comparisons are represented by these finite-stage comparisons independently of
further enlargement. For arbitrary presentations of the same common-stage object use
lem-weil-compact-support-finite-field-independence: the comparison is relative to the specified
representing isomorphisms and independent of the common overfield and arrow representatives.
Thus replacing a common-stage arrow by an equal representative gives the same cohomology
comparison and the same normalized open maps.
-/
theorem openExtension_tExact :
    IsNoetherian X ∧ QuasiCompact j ∧
    (letI : QuasiCompact j := quasiCompact D j
     ∃ S : SfCompactSupportCoefficientAction l D.k
         (PurCompactSupport.coefficientPrimeUnit l D hl) Ω
         (Compactification.ofIsOpenImmersion j),
       AllStages D l hl j Ω S ∧
       RepresentativeIndependence D l hl j Ω S) := by
  sorry

end WeilConjectures.ZlOpenTExact
