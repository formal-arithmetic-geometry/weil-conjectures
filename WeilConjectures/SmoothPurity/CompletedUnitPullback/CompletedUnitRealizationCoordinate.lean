/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.ConstantGeometricStalkUnit.IntegralConstantRegularReductionModel
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientChainNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! Strict finite-coordinate comparison for the completed pullback unit. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite coordinate of the normalized whole-system realization on the regular term. -/
def completedUnitRealizationCoordinate {X Y : Scheme.{u}} {g : X ⟶ Y}
    (c : Core l E g) (n : ℕ) :=
(coefficientSequenceProjection l E X n).app
      ((PrimitiveCounit.pull l E g).obj
        ((calculus l E Y).reduction.obj (integralConstantCoefficientObject l E Y))) ≫
    (coefficientFiniteDerivedRestriction l E X n).map
      ((coefficientSequenceDerivedEvaluation l E X n).map
        ((PrimitiveCounit.pull l E g).map c.reductionY.comparison.hom ≫ systemMap l E g) ≫
        (evaluationSingle l E X n).hom ≫
          (DerivedCategory.singleFunctor.{u + 2} (normalizedDVRModules l E X n) 0).map
            (c.reductionX.finite n).hom)

end WeilConjectures.CompletedUnitPullback

/-! The proof is elaborated in its own section: the local options and attributes below do not
reach the public definition and statement, which keep their original elaboration. -/

section CoordinateProof

set_option backward.defeqAttrib.useBackward true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem exact_square_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (V : B ⥤ D) (F : A ⥤ C) (R : C ⥤ D)
    [U.Additive] [V.Additive] [F.Additive] [R.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : U ⋙ V ≅ F ⋙ R) (M : A) :
    ((Functor.mapDerivedCategoryCompIso U V).symm ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryCompIso F R).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M) ≫
      R.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (R.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) =
    V.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem exact_square_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (V : B ⥤ D) (F : A ⥤ C) (R : C ⥤ D)
    [U.Additive] [V.Additive] [F.Additive] [R.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : U ⋙ V ≅ F ⋙ R) (K : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso U V).symm ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryCompIso F R).hom.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      V.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        V.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors U V K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance 5000] scalarReductionSourceDerived scalarReductionTargetDerived
  coefficientConstantTowerDerived
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.leftAdjoint
  limit coefficientConstantTowerProjection coefficientConstantTowerLimit
  pullbackLevelRegularIso pullbackUnitLevel
  constantWeilIntegralRoosComparison constantWeilIntegralLambda
  constantWeilDerivedCoefficientComparison constantWeilIntegralTheta constantWeilChainUnit
  finiteSingleRegularIso finiteRegularIso scalarReductionExistence scalarReductionExtension
  unrestrictedIntegralReductionExistence scalarReductionDerivedExistence
  PrimitiveCounit.inverse
  PrimitiveCounit.direct PrimitiveCounit.inverseEvaluation
  integralOperationsLevelPullback
  Scheme.coefficientProEtaleDirectRingMap coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf integralDerivedPullback integralDerivedPullbackComparison

attribute [local instance] PrimitiveCounit.levelAdditive PrimitiveCounit.levelLimits
  PrimitiveCounit.levelColimits scalarReductionExtensionAdditive
  scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf completedIntegralCommRingSheafUnrestricted
  SheafOfModules.instAbelian abelianOfAdjunction Abelian.ofCoimageImageComparisonIsIso
  scalarReductionSourceDerived scalarReductionTargetDerived coefficientConstantTowerDerived
  coefficientFiniteHasDerived coefficientSequenceHasDerived
  integralOperationsCommHasDerivedCategory integralTowerHasDerivedCategory
  integralCompletedRingHasDerivedCategory integralOperationsGoodComplex
  constantWeilIntegralComplex constantWeilIntegralGood integralConstantCoefficientObject
  quotientUnit coefficientFiniteAdjunction finiteConstantCoefficientObject
  coefficientFiniteDerivedExtension coefficientFiniteDerivedRestriction
  scalarReductionDerivedRestriction unrestrictedIntegralReductionFunctor
  integralOperationsGoodLocalization integralCoefficientSheafSystem
  completedIntegralCommRingProjectionUnrestricted integralOperationsPullbackOnGood
  integralOperationsPullbackComplexFunctor integralOperationsRoosFunctor integralOperationsRoos
  PrimitiveCounit.pull systemObject evaluationSingle coefficientSequenceLimit
  sheafCompose Functor.ofOpSequence Functor.ofSequence
  integralOperationsPullbackTowerFunctor integralOperationsPullbackLevel integralOperationsRestrict
  constantWeilPullbackTower constantWeilPullbackRoosEndomorphism
  PrimitiveCounit.RoosComparison roosF roosEval
  completedIntegralCoefficientSheafUnrestricted coefficientConstantTowerEvaluation
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors CochainComplex.singleFunctors
  DerivedCategory.Q DerivedCategory.Qh HomologicalComplexUpToQuasiIso.Qh
  HomotopyCategory.quotient Functor.mapHomotopyCategory Functor.mapHomologicalComplex
  HomologicalComplex.asFunctor SingleFunctors.postcomp

/-- The actual unshifted nth coordinate of the strict Roos cone. -/
private def roosCoordinate {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ) :
    integralOperationsRoosFunctor.obj T ⟶ T.obj (op n) := by
  unfold integralOperationsRoosFunctor integralOperationsRoos
  exact CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun j ↦ T.obj (op j)) (integralOperationsTowerStep T)) ≫
      Pi.π (fun j ↦ T.obj (op j)) n

private theorem roosCoordinate_iso
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {T T' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (z : T ≅ T') (n : ℕ) :
    integralOperationsRoosFunctor.map z.inv ≫ roosCoordinate T n ≫ z.hom.app (op n) =
      roosCoordinate T' n := by
  unfold roosCoordinate
  simp only [id_eq, Category.assoc]
  change integralOperationsRoosMap z.inv ≫
    CochainComplex.mappingCocone.fst _ ≫ Pi.π _ n ≫ z.hom.app (op n) = _
  rw [reassoc_of% (IntegralAmbient.roosMap_coordinates z.inv).1, Pi.map_π_assoc]
  simp only [Iso.inv_hom_id_app, Category.comp_id]

private def pullEvaluation {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    PrimitiveCounit.pull l E g ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙
        (integralOperationsLevelPullback l E g n).mapDerivedCategory := by
  letI : (integralOperationsLevelPullback l E g n).Additive :=
    PrimitiveCounit.levelAdditive l E g n
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelLimits l E g n
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelColimits l E g n
  exact (Functor.mapDerivedCategoryCompIso (PrimitiveCounit.inverse l E g)
      (coefficientSequenceEvaluation l E X n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (PrimitiveCounit.inverseEvaluation l E g n) ≪≫
      Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E Y n)
        (integralOperationsLevelPullback l E g n)

private theorem pullEvaluation_single {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E Y) :
    (pullEvaluation l E g n).hom.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (integralOperationsLevelPullback l E g n).mapDerivedCategory.map
          (((coefficientSequenceEvaluation l E Y n).mapDerivedCategorySingleFunctor 0).hom.app
            M) ≫
        ((integralOperationsLevelPullback l E g n).mapDerivedCategorySingleFunctor 0).hom.app
          ((coefficientSequenceEvaluation l E Y n).obj M) =
      (coefficientSequenceDerivedEvaluation l E X n).map
        (((PrimitiveCounit.inverse l E g).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      ((coefficientSequenceEvaluation l E X n).mapDerivedCategorySingleFunctor 0).hom.app
        ((PrimitiveCounit.inverse l E g).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((PrimitiveCounit.inverseEvaluation l E g n).hom.app M) := by
  have : (integralOperationsLevelPullback l E g n).Additive :=
    PrimitiveCounit.levelAdditive l E g n
  have : PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelLimits l E g n
  have : PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelColimits l E g n
  simpa only [pullEvaluation] using
    exact_square_single (PrimitiveCounit.inverse l E g)
      (coefficientSequenceEvaluation l E X n) (coefficientSequenceEvaluation l E Y n)
      (integralOperationsLevelPullback l E g n) (PrimitiveCounit.inverseEvaluation l E g n) M

private theorem systemMap_evaluation {X Y : Scheme.{u}} (g : X ⟶ Y)
    (c : Core l E g) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E X n).map (systemMap l E g) ≫
        (evaluationSingle l E X n).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (c.reductionX.finite n).hom =
      (pullEvaluation l E g n).hom.app (systemObject l E Y) ≫
        (integralOperationsLevelPullback l E g n).mapDerivedCategory.map
          ((evaluationSingle l E Y n).hom ≫
            (DerivedCategory.singleFunctor _ 0).map (c.reductionY.finite n).hom) ≫
        ((integralOperationsLevelPullback l E g n).mapDerivedCategorySingleFunctor 0).hom.app
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫
        (DerivedCategory.singleFunctor _ 0).map (finiteMultiplication l E g n) := by
  have : (integralOperationsLevelPullback l E g n).Additive :=
    PrimitiveCounit.levelAdditive l E g n
  have : PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelLimits l E g n
  have : PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelColimits l E g n
  simp only [Functor.map_comp, Category.assoc]
  have hn := ((integralOperationsLevelPullback l E g n).mapDerivedCategorySingleFunctor
    0).hom.naturality (c.reductionY.finite n).hom
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [reassoc_of% pullEvaluation_single l E g n (systemUnit l E Y)]
  simp only [systemMap, Functor.map_comp, Category.assoc, evaluationSingle]
  have hn' := ((coefficientSequenceEvaluation l E X n).mapDerivedCategorySingleFunctor
    0).hom.naturality (systemMultiplication l E g)
  simp only [Functor.comp_map] at hn'
  erw [reassoc_of% hn']
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    c.finite_components n]

private theorem restricted_projection_factors (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (coefficientSequenceProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) =
      (coefficientConstantTowerProjection l E W n).app
          ((coefficientSequenceDerivedRestriction l E W).obj (DerivedCategory.Q.obj C)) ≫
        (coefficientConstantTowerEvaluation l E W n).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app C) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app
          ((PrimitiveCounit.restrictComplex l E W).obj C) ≫
        DerivedCategory.Q.map (PrimitiveCounit.restrictEvaluation l E W C n).hom := by
  have h := exact_square_factors (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) C
  unfold coefficientSequenceProjection
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  exact congrArg (fun t ↦
    (coefficientConstantTowerProjection l E W n).app
      ((coefficientSequenceDerivedRestriction l E W).obj (DerivedCategory.Q.obj C)) ≫ t) h

set_option maxHeartbeats 1600000 in
-- The projected localization identity carries large concrete sheaf and tower instance terms.
private theorem pull_model_projection {X Y : Scheme.{u}} (g : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y)
    (ρ : PrimitiveCounit.RoosRealization l E X)
    (r : integralDerivedPullback l E g ≅
      S.reduction ⋙ PrimitiveCounit.pull l E g ⋙ coefficientSequenceLimit l E X)
    (hr : PrimitiveCounit.PullModel l E g S ρ r)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    ∃ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj),
      CoefficientReductionPresentation l E Y S P.obj P.property.1 C eC κ ∧
      ∀ n : ℕ,
        r.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientSequenceProjection l E X n).app
            ((PrimitiveCounit.pull l E g).obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫
          (coefficientFiniteDerivedRestriction l E X n).map
            ((coefficientSequenceDerivedEvaluation l E X n).map
              ((PrimitiveCounit.pull l E g).map eC.hom ≫
                (PrimitiveCounit.inverse l E g).mapDerivedCategoryFactors.hom.app C) ≫
              (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
                (((PrimitiveCounit.inverse l E g).mapHomologicalComplex (.up ℤ)).obj C)) ≫
          (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
            (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj
              (((PrimitiveCounit.inverse l E g).mapHomologicalComplex (.up ℤ)).obj C)) ≫
          DerivedCategory.Q.map
            (((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
              ((PrimitiveCounit.inverseComplexEvaluation l E g n).hom.app C ≫
                ((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).map
                  (κ n).hom)) =
        (integralDerivedPullbackComparison l E g).hom.app P ≫
          DerivedCategory.Q.map
            (roosCoordinate ((integralOperationsPullbackTowerFunctor l E g).obj P.obj) n) := by
  obtain ⟨C, eC, κ, z, hp, hz, hm⟩ := hr P
  refine ⟨C, eC, κ, hp, ?_⟩
  intro n
  let I := ((PrimitiveCounit.inverse l E g).mapHomologicalComplex (.up ℤ)).obj C
  let Z := (PrimitiveCounit.restrictComplex l E X).obj I
  let a := (PrimitiveCounit.pull l E g).map eC.hom ≫
    (PrimitiveCounit.inverse l E g).mapDerivedCategoryFactors.hom.app C
  have hproj := ρ.projection Z n
  have h := congrArg (fun t ↦ t ≫ ρ.comparison.hom.app Z ≫
    (coefficientConstantTowerProjection l E X n).app (DerivedCategory.Q.obj Z) ≫
    (coefficientConstantTowerEvaluationFactors l E X n).hom.app Z) hm
  simp only [Category.assoc] at h
  erw [Iso.inv_hom_id_app_assoc] at h
  erw [hproj] at h
  have hf := restricted_projection_factors l E X I n
  change r.hom.app _ ≫ (coefficientSequenceProjection l E X n).app _ ≫
    (coefficientFiniteDerivedRestriction l E X n).map
      ((coefficientSequenceDerivedEvaluation l E X n).map a ≫ _) ≫ _ ≫ _ = _
  rw [(coefficientFiniteDerivedRestriction l E X n).map_comp]
  simp only [Category.assoc]
  have hnat := (coefficientSequenceProjection l E X n).naturality a
  simp only [Functor.comp_map] at hnat
  erw [← reassoc_of% hnat]
  rw [reassoc_of% hf]
  rw [← DerivedCategory.Q.map_comp]
  rw [← hz n]
  erw [← (coefficientConstantTowerProjection l E X n).naturality_assoc
    ((coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.hom.app I)]
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
    (coefficientConstantTowerLimit l E X).map
      ((coefficientSequenceDerivedRestriction l E X).map a) ≫
    (coefficientConstantTowerLimit l E X).map
      ((coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.hom.app I) ≫
    (coefficientConstantTowerProjection l E X n).app (DerivedCategory.Q.obj Z) ≫
    (coefficientConstantTowerEvaluationFactors l E X n).hom.app Z ≫
    DerivedCategory.Q.map (z.hom.app (op n)) = _
  rw [← Functor.map_comp_assoc]
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
    (coefficientConstantTowerLimit l E X).map
      (PrimitiveCounit.pullRestrictionIso l E g S P.obj C eC).hom ≫
    (coefficientConstantTowerProjection l E X n).app (DerivedCategory.Q.obj Z) ≫
    (coefficientConstantTowerEvaluationFactors l E X n).hom.app Z ≫
    DerivedCategory.Q.map (z.hom.app (op n)) = _
  rw [← reassoc_of% h]
  have hroos : integralOperationsRoosFunctor.map z.inv ≫
      (PrimitiveCounit.roosBridge l E X Z).hom ≫ roosEval Z n ≫ z.hom.app (op n) =
    CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun j ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P.obj).obj (op j))
        (integralOperationsTowerStep
          ((integralOperationsPullbackTowerFunctor l E g).obj P.obj))) ≫
      Pi.π (fun j ↦
        ((integralOperationsPullbackTowerFunctor l E g).obj P.obj).obj (op j)) n := by
    simp only [PrimitiveCounit.roosBridge, Iso.refl_hom]
    change integralOperationsRoosFunctor.map z.inv ≫
      roosCoordinate Z.asFunctor n ≫ z.hom.app (op n) = _
    exact roosCoordinate_iso z n
  simpa only [roosCoordinate, id_eq, Functor.mapIso_hom, Iso.symm_hom,
    ← DerivedCategory.Q.map_comp, Category.assoc] using!
    congrArg (fun t ↦ (integralDerivedPullbackComparison l E g).hom.app P ≫
      DerivedCategory.Q.map t) hroos

private theorem pullEvaluation_factors {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (pullEvaluation l E g n).hom.app (DerivedCategory.Q.obj C) ≫
        (integralOperationsLevelPullback l E g n).mapDerivedCategory.map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C) ≫
        (integralOperationsLevelPullback l E g n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((PrimitiveCounit.inverse l E g).mapDerivedCategoryFactors.hom.app C) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
          (((PrimitiveCounit.inverse l E g).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((PrimitiveCounit.inverseComplexEvaluation l E g n).hom.app C) := by
  have : (integralOperationsLevelPullback l E g n).Additive :=
    PrimitiveCounit.levelAdditive l E g n
  have : PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelLimits l E g n
  have : PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelColimits l E g n
  have h := exact_square_factors (PrimitiveCounit.inverse l E g)
    (coefficientSequenceEvaluation l E X n) (coefficientSequenceEvaluation l E Y n)
    (integralOperationsLevelPullback l E g n) (PrimitiveCounit.inverseEvaluation l E g n) C
  have he : (PrimitiveCounit.inverseComplexEvaluation l E g n).hom.app C =
      (NatTrans.mapHomologicalComplex (PrimitiveCounit.inverseEvaluation l E g n).hom
        (.up ℤ)).app C := by
    ext i : 1
    simp only [PrimitiveCounit.inverseComplexEvaluation, Functor.mapHomologicalComplexCompIso,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.comp_id]
  simpa only [pullEvaluation, he] using h

set_option maxHeartbeats 1600000 in
-- The two exact-functor squares require elaborating the full coefficient-system model.
private theorem model_finite_coordinate {X Y : Scheme.{u}} (g : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y)
    (ρ : PrimitiveCounit.RoosRealization l E X)
    (r : integralDerivedPullback l E g ≅
      S.reduction ⋙ PrimitiveCounit.pull l E g ⋙ coefficientSequenceLimit l E X)
    (hr : PrimitiveCounit.PullModel l E g S ρ r)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceProjection l E X n).app
        ((PrimitiveCounit.pull l E g).obj (S.reduction.obj (DerivedCategory.Q.obj P.obj))) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        ((pullEvaluation l E g n).hom.app (S.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
          (integralOperationsLevelPullback l E g n).mapDerivedCategory.map
            ((S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj) ≫
              (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom) ≫
          (integralOperationsLevelPullback l E g n).mapDerivedCategoryFactors.hom.app
            (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
        (((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).obj
          (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj)) =
    (integralDerivedPullbackComparison l E g).hom.app P ≫
      DerivedCategory.Q.map
        (roosCoordinate ((integralOperationsPullbackTowerFunctor l E g).obj P.obj) n) := by
  have : (integralOperationsLevelPullback l E g n).Additive :=
    PrimitiveCounit.levelAdditive l E g n
  have : PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelLimits l E g n
  have : PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelColimits l E g n
  obtain ⟨C, eC, κ, hp, hproj⟩ := pull_model_projection l E g S ρ r hr P
  have hκ := hp.1 n
  change (coefficientSequenceDerivedEvaluation l E Y n).map eC.hom ≫
    (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
    DerivedCategory.Q.map (κ n).hom = _ at hκ
  let F := integralOperationsLevelPullback l E g n
  let R := scalarReductionRestriction l E X n
  have hfin :
      (pullEvaluation l E g n).hom.app (S.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
        F.mapDerivedCategory.map ((S.reductionEvaluation n).hom.app
          (DerivedCategory.Q.obj P.obj) ≫
          (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom) ≫
        F.mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj) =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((PrimitiveCounit.pull l E g).map eC.hom ≫
          (PrimitiveCounit.inverse l E g).mapDerivedCategoryFactors.hom.app C) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
          (((PrimitiveCounit.inverse l E g).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((PrimitiveCounit.inverseComplexEvaluation l E g n).hom.app C ≫
            (F.mapHomologicalComplex (.up ℤ)).map (κ n).hom) := by
    rw [← hκ]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapDerivedCategoryFactors_hom_naturality]
    have hn := (pullEvaluation l E g n).hom.naturality eC.hom
    simp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    rw [reassoc_of% pullEvaluation_factors l E g n C]
  rw [hfin]
  simp only [(coefficientFiniteDerivedRestriction l E X n).map_comp, Category.assoc]
  erw [R.mapDerivedCategoryFactors_hom_naturality]
  simpa only [Functor.map_comp, Category.assoc] using hproj n

private theorem regular_reduction (W : Scheme.{u}) (n : ℕ) :
    (coefficientFiniteReductionModel l E W (constantWeilIntegralComplex l E W)
      (constantWeilIntegralGood l E W).property.1 n).hom ≫
        DerivedCategory.Q.map (finiteSingleRegularIso l E W n).hom =
      constantCoefficientReductionMap l E W n := by
  exact ConstantGeometricStalkUnit.regular_reduction_model l E W n

private theorem finiteMultiplication_regular {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) : finiteMultiplication l E g n = (finitePullbackRegularIso l E g n).hom := by
  rfl

set_option maxHeartbeats 1600000 in
-- The regular-coordinate calculation combines three localization and single-complex squares.
private theorem regular_model_coordinate {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (c : Core l E g) (n : ℕ) :
    c.realization.hom.app (integralConstantCoefficientObject l E Y) ≫
      (coefficientSequenceProjection l E X n).app
        ((PrimitiveCounit.pull l E g).obj
          ((calculus l E Y).reduction.obj (integralConstantCoefficientObject l E Y))) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        ((pullEvaluation l E g n).hom.app
            ((calculus l E Y).reduction.obj (integralConstantCoefficientObject l E Y)) ≫
          (integralOperationsLevelPullback l E g n).mapDerivedCategory.map
            (((calculus l E Y).reductionEvaluation n).hom.app
                (integralConstantCoefficientObject l E Y) ≫
              constantCoefficientReductionMap l E Y n) ≫
          ((integralOperationsLevelPullback l E g n).mapDerivedCategorySingleFunctor 0).hom.app
            (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫
          (DerivedCategory.singleFunctor _ 0).map (finiteMultiplication l E g n)) ≫
      ((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)) =
    (integralDerivedPullbackComparison l E g).hom.app (constantWeilIntegralGood l E Y) ≫
      DerivedCategory.Q.map
        (roosCoordinate (constantWeilPullbackTower l E g) n ≫
          (pullbackLevelRegularIso l E g n).hom) := by
  change c.realization.hom.app ((DerivedCategory.Q.obj (constantWeilIntegralComplex l E Y))) ≫
      (coefficientSequenceProjection l E X n).app
        ((PrimitiveCounit.pull l E g).obj
          ((calculus l E Y).reduction.obj
          ((DerivedCategory.Q.obj (constantWeilIntegralComplex l E Y))))) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        ((pullEvaluation l E g n).hom.app
            ((calculus l E Y).reduction.obj
              ((DerivedCategory.Q.obj (constantWeilIntegralComplex l E Y)))) ≫
          (integralOperationsLevelPullback l E g n).mapDerivedCategory.map
            (((calculus l E Y).reductionEvaluation n).hom.app
                ((DerivedCategory.Q.obj (constantWeilIntegralComplex l E Y))) ≫
              constantCoefficientReductionMap l E Y n) ≫
          ((integralOperationsLevelPullback l E g n).mapDerivedCategorySingleFunctor 0).hom.app
            (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫
          (DerivedCategory.singleFunctor _ 0).map (finiteMultiplication l E g n)) ≫
      ((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)) =
    (integralDerivedPullbackComparison l E g).hom.app (constantWeilIntegralGood l E Y) ≫
      DerivedCategory.Q.map
        (roosCoordinate (constantWeilPullbackTower l E g) n ≫
          (pullbackLevelRegularIso l E g n).hom)
  have : (integralOperationsLevelPullback l E g n).Additive :=
    PrimitiveCounit.levelAdditive l E g n
  have : PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelLimits l E g n
  have : PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelColimits l E g n
  have h := model_finite_coordinate l E g
    (calculus l E Y).toCoefficientDerivedSystemReduction c.roos c.realization
    c.realization_model (constantWeilIntegralGood l E Y) n
  have h' := congrArg (fun t ↦ t ≫ DerivedCategory.Q.map
    (((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
      (((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).map
        (finiteSingleRegularIso l E Y n).hom ≫
        ((integralOperationsLevelPullback l E g n).mapCochainComplexSingleFunctor 0).hom.app
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫
        (CochainComplex.singleFunctor _ 0).map (finiteMultiplication l E g n)) ≫
      ((scalarReductionRestriction l E X n).mapCochainComplexSingleFunctor 0).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)))) h
  simp only [Category.assoc, DerivedCategory.Q.map_comp] at h'
  rw [← regular_reduction l E Y n]
  simp only [(integralOperationsLevelPullback l E g n).mapDerivedCategory.map_comp,
    Category.assoc]
  rw [(integralOperationsLevelPullback l E g n).mapDerivedCategorySingleFunctor_hom_app_eq
    (SheafOfModules.unit (integralCoefficientSheaf l E Y n))]
  simp only [Category.assoc]
  erw [reassoc_of% Functor.mapDerivedCategoryFactors_hom_naturality
    (integralOperationsLevelPullback l E g n) (finiteSingleRegularIso l E Y n).hom]
  rw [(scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor_hom_app_eq
    (SheafOfModules.unit (integralCoefficientSheaf l E X n))]
  simp only [(coefficientFiniteDerivedRestriction l E X n).map_comp, Category.assoc]
  repeat erw [(scalarReductionRestriction l E X n).mapDerivedCategoryFactors_hom_naturality_assoc]
  simpa only [pullbackLevelRegularIso, Iso.trans_hom, Functor.mapIso_hom,
    finiteMultiplication_regular, Functor.map_comp, Category.assoc] using! h'

private theorem strict_unit_projection {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (n : ℕ) :
    (integralDerivedPullbackComparison l E g).hom.app (constantWeilIntegralGood l E Y) ≫
      DerivedCategory.Q.map
        (roosCoordinate (constantWeilPullbackTower l E g) n ≫
          (pullbackLevelRegularIso l E g n).hom) =
    (ConstantGeometricStalkUnit.integralUnit l E g).hom ≫
      (DerivedCategory.singleFunctor _ 0).map (constantCoefficientProjection l E X n) := by
  unfold roosCoordinate
  rw [ConstantGeometricStalkUnit.integralUnit_canonicalWeil]
  simp only [constantWeilIntegralTheta, constantWeilIntegralLambda, Iso.trans_hom,
    Category.assoc]
  apply (cancel_epi (constantWeilIntegralRoosComparison l E g).inv).mp
  simp only [constantWeilIntegralRoosComparison, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv, Iso.app_inv, Iso.app_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]
  erw [Iso.inv_hom_id_assoc]
  simp only [id_eq]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  simpa only [Category.assoc, constantWeilPullbackRoosEndomorphism] using!
    (congrArg (fun t ↦ t ≫ (pullbackLevelRegularIso l E g n).hom)
      (coefficientChainUnit_projection l E g n)).trans
        (pullbackLevelRegularIso_projection l E g n)

private theorem completedUnitRealizationCoordinate_eq_integralUnit_aux
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (c : Core l E g) (n : ℕ) :
    c.realization.hom.app (integralConstantCoefficientObject l E Y) ≫
        completedUnitRealizationCoordinate l E c n =
      (ConstantGeometricStalkUnit.integralUnit l E g).hom ≫
        (DerivedCategory.singleFunctor.{u + 2} _ 0).map
          (constantCoefficientProjection l E X n) ≫
        ((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).inv.app
          (SheafOfModules.unit (integralCoefficientSheaf l E X n)) := by
  have : (integralOperationsLevelPullback l E g n).Additive :=
    PrimitiveCounit.levelAdditive l E g n
  have : PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelLimits l E g n
  have : PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
    PrimitiveCounit.levelColimits l E g n
  have hfinite :
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((PrimitiveCounit.pull l E g).map c.reductionY.comparison.hom ≫ systemMap l E g) ≫
        (evaluationSingle l E X n).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (c.reductionX.finite n).hom =
      (pullEvaluation l E g n).hom.app
          ((calculus l E Y).reduction.obj (integralConstantCoefficientObject l E Y)) ≫
        (integralOperationsLevelPullback l E g n).mapDerivedCategory.map
          (((calculus l E Y).reductionEvaluation n).hom.app
              (integralConstantCoefficientObject l E Y) ≫
            constantCoefficientReductionMap l E Y n) ≫
        ((integralOperationsLevelPullback l E g n).mapDerivedCategorySingleFunctor 0).hom.app
          (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫
        (DerivedCategory.singleFunctor _ 0).map (finiteMultiplication l E g n) := by
    rw [Functor.map_comp, Category.assoc, systemMap_evaluation l E g c n]
    have hn := (pullEvaluation l E g n).hom.naturality c.reductionY.comparison.hom
    simp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    simp only [← Functor.map_comp_assoc]
    rw [c.reductionY.reduction n]
  apply (cancel_mono
    (((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).hom.app
      (SheafOfModules.unit (integralCoefficientSheaf l E X n)))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  unfold completedUnitRealizationCoordinate
  rw [hfinite]
  simp only [Category.assoc]
  erw [Category.comp_id]
  exact (regular_model_coordinate l E g c n).trans (strict_unit_projection l E g n)

end WeilConjectures.CompletedUnitPullback

end CoordinateProof

namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/--
The strict PullModel witness identifies the regular finite coordinate with the
canonical integral unit coordinate.  This is the representative replacement and
whole-system Roos comparison before extensionality of the completed object.
(blueprint: new-lem-pur-completed-unit-realization-coordinate).
-/
theorem completedUnitRealizationCoordinate_eq_integralUnit
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (c : Core l E g) (n : ℕ) :
    c.realization.hom.app (integralConstantCoefficientObject l E Y) ≫
        completedUnitRealizationCoordinate l E c n =
      (ConstantGeometricStalkUnit.integralUnit l E g).hom ≫
        (DerivedCategory.singleFunctor.{u + 2} _ 0).map
          (constantCoefficientProjection l E X n) ≫
        ((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).inv.app
          (SheafOfModules.unit (integralCoefficientSheaf l E X n)) :=
  completedUnitRealizationCoordinate_eq_integralUnit_aux l E g c n

end WeilConjectures.CompletedUnitPullback
