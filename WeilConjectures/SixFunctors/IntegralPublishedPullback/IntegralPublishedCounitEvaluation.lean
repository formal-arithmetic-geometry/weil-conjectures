/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
import all WeilConjectures.SixFunctors.IntegralPublishedPullback.IntegralPublishedTowerEvaluation
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientNormalization

/-! # Finite evaluation of the published completed pullback counit

Source: Stacks 0941 and 099N, coefficient adjunction and normalized quotient presentation.
(blueprint: lem-sf-integral-published-counit-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.integralDerivedPullback WeilConjectures.pullbackTensorCalculus
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.integralComparisonDerivedSequencePullback
  WeilConjectures.coefficientConstantTowerLimit
  WeilConjectures.coefficientConstantTowerEvaluation
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.integralOperationsRoos WeilConjectures.integralOperationsRoosFunctor
  WeilConjectures.integralOperationsGoodComplex
  WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.integralOperationsPullbackOnGood
  WeilConjectures.integralOperationsPullbackComplexFunctor
  WeilConjectures.integralPullbackFiniteComplex
  WeilConjectures.integralOperationsPullbackTowerFunctor
  WeilConjectures.integralOperationsPullbackLevel WeilConjectures.integralOperationsRestrict
  WeilConjectures.scalarReductionDerivedRestriction
  HomologicalComplex.complexOfFunctorsToFunctorToComplex HomologicalComplex.asFunctor
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.pullbackTensorConstantLimit WeilConjectures.pullbackTensorTowerQ
  WeilConjectures.pullbackTensorRestrictedTower
  WeilConjectures.pullbackTensorSequenceDerived
  WeilConjectures.pullbackTensorReferencePullback
  CochainComplex.IsKFlatResolutionIndependentCoefficients
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPublishedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem evaluated_counit_adjunct (W : Scheme.{u})
    (T : CoefficientDerivedSystemCalculus l E W)
    {A : DerivedCategory (scalarReductionSource l E W)}
    (N : coefficientSequenceDerived l E W)
    (a : A ⟶ (coefficientSequenceLimit l E W).obj N) (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).homEquiv _ _
      ((T.reductionEvaluation n).inv.app A ≫
        (coefficientSequenceDerivedEvaluation l E W n).map
          (T.reduction.map a ≫ T.adjunction.counit.app N)) =
      a ≫ (coefficientSequenceProjection l E W n).app N := by
  rw [Functor.map_comp, ← Category.assoc]
  have hn := (T.reductionEvaluation n).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc, Adjunction.homEquiv_naturality_left,
    T.counit_projection]

/-- Finite evaluation of reduction of the published pullback model followed by the counit.
Source: Stacks 0941 and 099N. Choose the prescribed ordinary quotient presentation;
its normalization and finite evaluation determine the finite pullback component.
Project the published Roos realization through that component. Taking adjoints by
the finite scalar adjunction and counit_projection gives the specified
integralPullbackFiniteComparison. Naturality transports the representative to K.
(blueprint: lem-sf-integral-published-counit-evaluation). -/
theorem published_counit_finite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :
    ((pullbackTensorCalculus l E X).reductionEvaluation n).inv.app
        ((integralDerivedPullback l E f).obj K.obj) ≫
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorCalculus l E X).reduction.map
            ((pullbackTensorIntegralPullbackModel l E f).hom.app K.obj) ≫
          (pullbackTensorCalculus l E X).adjunction.counit.app
            ((pullbackTensorSequenceDerived l E f).obj
              ((pullbackTensorCalculus l E Y).reduction.obj K.obj))) ≫
      (pullbackTensorDerivedEvaluation l E f n).hom.app
        ((pullbackTensorCalculus l E Y).reduction.obj K.obj) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).reductionEvaluation n).hom.app K.obj ≫
          (scalarReductionDerivedExtension l E Y n).map e.inv ≫
          (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom) ≫
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
          ).mapDerivedCategoryFactors.hom.app
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
          (.up ℤ)).inv.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) =
    integralPullbackFiniteComparison l E f K.obj P e n := by
  let S := pullbackTensorCalculus l E Y
  let T := pullbackTensorCalculus l E X
  let C := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj
  let D := ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj C
  let F := pullbackTensorSequenceDerived l E f
  let V := coefficientSequenceDerivedEvaluation l E X n
  let R := coefficientFiniteDerivedRestriction l E X n
  let B := finiteDerivedPullback l E n f
  let β := pullbackTensorDerivedEvaluation l E f n
  let a := F.map ((pullbackTensorReductionModel l E Y).hom.app P) ≫
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C
  let c := (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
      ).mapDerivedCategoryFactors.hom.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj) ≫
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
        (.up ℤ)).inv.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj))
  let b := β.hom.app (S.reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
    B.map (((S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj)) ≫
      (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom) ≫ c
  obtain ⟨_, _, _, hp, _⟩ := CompletedQuotient.completedComparisonQuotientNormalization
    l E (𝟙 X) f (fun _ ↦ K) (fun _ ↦ P) (fun _ ↦ e)
  have hpres := (hp 0).1 n
  change CoefficientComparisonEquation _ _ _ _ _ at hpres
  unfold CoefficientComparisonEquation at hpres
  have hf : V.map a ≫
      V.map ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.inv.app C) ≫
      β.hom.app (DerivedCategory.Q.obj C) ≫
      B.map ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map ((pullbackTensorReductionEvaluationComplex l E Y n).inv.app P.obj)) ≫
      c = b := by
    dsimp only [a, b]
    have hc : V.map ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app C) ≫
      V.map ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.inv.app C) = 𝟙 _ := by
      rw [← V.map_comp, Iso.hom_inv_id_app, V.map_id]
    simp only [V.map_comp, Category.assoc]
    erw [reassoc_of% hc]
    erw [reassoc_of% (β.hom.naturality ((pullbackTensorReductionModel l E Y).hom.app P))]
    dsimp only [B]
    simp only [← Functor.map_comp_assoc]
    erw [hpres]
    rfl
  have hm : (pullbackTensorIntegralPullbackModel l E f).hom.app
        (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceLimit l E X).map a ≫
      (pullbackTensorLimitRoos l E X D).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map
        (pullbackTensorPullbackTower l E f P.obj).hom) =
    (integralDerivedPullbackComparison l E f).hom.app P := by
    have h := (pullbackTensorIntegralPullbackModel_existsUnique l E f).exists.choose_spec P
    change (pullbackTensorIntegralPullbackModel l E f).app (DerivedCategory.Q.obj P.obj) = _ at h
    have h' := congrArg (fun i ↦ i.hom ≫
      (pullbackTensorReferencePullbackModel l E f P).hom) h
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at h'
    dsimp only [pullbackTensorReferencePullbackModel] at h'
    simpa only [a, D, C, F,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc] using h'
  have hproj : (pullbackTensorIntegralPullbackModel l E f).hom.app
      (DerivedCategory.Q.obj P.obj) ≫
      (coefficientSequenceProjection l E X n).app (F.obj (S.reduction.obj
        (DerivedCategory.Q.obj P.obj))) ≫ R.map b =
    (integralDerivedPullbackComparison l E f).hom.app P ≫
      integralOperationRoosProjection l E X
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (integralPullbackFiniteComplex l E f P.obj n) := by
    have h := congrArg (fun t ↦ t ≫ integralOperationRoosProjection l E X
      ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
        (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
          (integralPullbackFiniteComplex l E f P.obj n)) hm
    simp only [Category.assoc] at h
    erw [reassoc_of% (roos_projection_natural l E
      (pullbackTensorPullbackTower l E f P.obj).hom n)] at h
    erw [reassoc_of% (published_bridge_projection l E X D n)] at h
    erw [reassoc_of% ((coefficientSequenceProjection l E X n).naturality a)] at h
    have hq := (pullbackTensorPullbackTower_existsUnique l E f P.obj).exists.choose_spec n
    change (pullbackTensorPullbackTower l E f P.obj).app (op n) = _ at hq
    have hqh := congrArg Iso.hom hq
    change (pullbackTensorPullbackTower l E f P.obj).hom.app (op n) = _ at hqh
    rw [hqh] at h
    erw [published_tower_finite_component l E f P.obj n] at h
    rw [← R.map_comp, hf] at h
    exact h
  let bK := β.hom.app (S.reduction.obj K.obj) ≫
    B.map (((S.reductionEvaluation n).hom.app K.obj) ≫
      (scalarReductionDerivedExtension l E Y n).map e.inv ≫
      (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom) ≫ c
  have hb : V.map (F.map (S.reduction.map e.inv)) ≫ b = bK := by
    dsimp only [b, bK]
    erw [reassoc_of% (β.hom.naturality (S.reduction.map e.inv))]
    dsimp only [B]
    simp only [← Functor.map_comp_assoc]
    erw [reassoc_of% ((S.reductionEvaluation n).hom.naturality e.inv)]
    rfl
  apply ((coefficientFiniteAdjunction l E X n).homEquiv _ _).injective
  change (coefficientFiniteAdjunction l E X n).homEquiv _ _
    ((T.reductionEvaluation n).inv.app ((integralDerivedPullback l E f).obj K.obj) ≫
      V.map (T.reduction.map ((pullbackTensorIntegralPullbackModel l E f).hom.app K.obj) ≫
        T.adjunction.counit.app (F.obj (S.reduction.obj K.obj))) ≫ bK) = _
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
    evaluated_counit_adjunct l E X T]
  unfold integralPullbackFiniteComparison
  dsimp only [coefficientFiniteAdjunction]
  erw [Equiv.apply_symm_apply]
  rw [← hb, R.map_comp, Category.assoc]
  erw [← (coefficientSequenceProjection l E X n).naturality_assoc]
  rw [← Category.assoc]
  erw [← (pullbackTensorIntegralPullbackModel l E f).hom.naturality e.inv]
  simp only [Category.assoc]
  rw [hproj]

end WeilConjectures.IntegralPublishedPullback
