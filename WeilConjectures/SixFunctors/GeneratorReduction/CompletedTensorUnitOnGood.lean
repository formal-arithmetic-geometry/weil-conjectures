/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationConstruction
import all WeilConjectures.SixFunctors.GeneratorReduction.TensorQuotientAugmentationOnGood

/-! # The ordinary-to-completed tensor unit on good complexes

On good complexes `P` and `Q`, the ordinary-to-completed tensor unit
`podCompletedTensorUnit`, conjugated by the ordinary total tensor model and the completed tensor
comparison, is the localization of the strict quotient augmentation of `P ⊗ Q`.

## Implementation details

This is `tensorQuotientTranspose_onGood` with the identity ordinary tensor representative, followed
by the normalization of the integral tensor model.

## References

* Stacks Project, Tags 07A4, 07A6, 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  StrictTensorAugmentation.map
attribute [local implicit_reducible] PurCompactSupport.completed
  integralOperationsGoodLocalization
  pullbackTensorOrdinaryLimit pullbackTensorConstantLimit pullbackTensorTowerQ
  coefficientConstantTowerLimit coefficientSequenceLimit
  integralOperationsTensorComplexFunctor integralOperationsRoos integralOperationsRoosFunctor
  IntegralOnSlice.Site IntegralOnSlice.topology IntegralOnSlice.ring IntegralOnSlice.Good
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] CoefficientTensorModels.iso
  CoefficientClosedStructure.tensor pullbackTensorCalculus
  integralOperationsTensorTowerFunctor integralOperationsRoos integralOperationsRoosMap
attribute [local implicit_reducible] integralOperationsTensorOnGood
  pullbackTensorReferenceTensor pullbackTensorRestrictedTower
attribute [local irreducible] pullbackTensorReferenceTensorModel pullbackTensorLimitRoos

private theorem cancel_iso_aux {C : Type*} [Category C] {a b Y Z e : C} (f : a ⟶ b)
    (g : b ⟶ Y) (i : Z ≅ Y) (k : Y ⟶ e) : (f ≫ g ≫ i.inv) ≫ i.hom ≫ k = f ≫ g ≫ k := by
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On good complexes, the ordinary-to-completed tensor unit, conjugated by the ordinary total
tensor model and the completed tensor comparison, is the strict quotient augmentation. -/
theorem podCompletedTensorUnit_onGood (X : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    ((pullbackTensorCalculus l E X).integralTensorModel.iso (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)
        (pullbackTensorCalculus l E X).integralClosed
        P.obj Q.obj P.property.1 Q.property.1).hom ≫
      podCompletedTensorUnit l E X (DerivedCategory.Q.obj P.obj)
        (DerivedCategory.Q.obj Q.obj) ≫
      (integralCompletedTensorComparison l E X).hom.app (P, Q) =
      DerivedCategory.Q.map ((StrictTensorAugmentation.map l E X).app (P.obj, Q.obj)) := by
  let S := pullbackTensorCalculus l E X
  let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)).obj (P.obj, Q.obj)
  have hT : integralOperationsGoodComplex l E X T :=
    IntegralAmbient.tensor_good l E X P.obj Q.obj P.property Q.property
  obtain ⟨ψ, hψ, hfinite⟩ := tensorReduction_ordinaryModel l E X P Q hT
  have hc := tensorReduction_ordinaryTranspose l E X P.obj Q.obj ψ hfinite
  let G := (pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)
  let B := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)).obj (G.obj P.obj, G.obj Q.obj)
  let β := (S.integralTensorModel.iso (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X) S.integralClosed
    P.obj Q.obj P.property.1 Q.property.1).hom
  let δ := S.reductionTensor.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
  let χ := S.systemClosed.tensor.map
    (Prod.mkHom ((pullbackTensorReductionModel l E X).hom.app P)
      ((pullbackTensorReductionModel l E X).hom.app Q))
  let τ := (pullbackTensorSystemModel l E X _ _
    (pullbackTensorReductionGood l E X P) (pullbackTensorReductionGood l E X Q)).inv
  have hcanon : S.reduction.map β ≫ δ ≫ χ ≫ τ =
      (pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫ DerivedCategory.Q.map ψ := hψ
  have hm : S.reduction.map β ≫ S.reduction.map (𝟙 _) ≫ δ ≫ χ ≫ τ =
      (pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫ DerivedCategory.Q.map ψ := by
    rw [S.reduction.map_id, Category.id_comp]
    exact hcanon
  have ht := GeneratorReduction.transpose_roos l E X ⟨T, hT⟩ B ψ
  -- The normalization of the integral tensor model.
  let e := pullbackTensorReferenceTensorModel l E X P Q
  have hmodel : (pullbackTensorIntegralTensorModel l E X).hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫ e.hom =
      (integralCompletedTensorComparison l E X).hom.app (P, Q) := by
    have h := congrArg Iso.hom
      ((pullbackTensorIntegralTensorModel_existsUnique l E X).exists.choose_spec P Q)
    simpa only [pullbackTensorIntegralTensorModel, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, e] using
      congrArg (fun z ↦ z ≫ e.hom) h
  have hunit : podCompletedTensorUnit l E X (DerivedCategory.Q.obj P.obj)
        (DerivedCategory.Q.obj Q.obj) ≫
      (integralCompletedTensorComparison l E X).hom.app (P, Q) =
      S.adjunction.unit.app _ ≫ (coefficientSequenceLimit l E X).map δ ≫ e.hom := by
    rw [← hmodel]
    unfold podCompletedTensorUnit
    with_unfolding_all exact
      cancel_iso_aux _ _ ((pullbackTensorIntegralTensorModel l E X).app _) e.hom
  refine Eq.trans (congrArg (fun z ↦ β ≫ z) hunit) ?_
  have h₁ := GeneratorReduction.unit_reference_transport S.reduction
    (coefficientSequenceLimit l E X) S.adjunction β (𝟙 _) δ χ τ
    ((pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫ DerivedCategory.Q.map ψ)
    (pullbackTensorLimitRoos l E X B).hom
    (DerivedCategory.Q.map
      (integralOperationsRoosMap (pullbackTensorTensorTower l E X P.obj Q.obj).hom))
    e.hom hm (GeneratorReduction.reference_model_hom l E X P Q)
  rw [S.reduction.map_id, Category.id_comp] at h₁
  refine h₁.trans ?_
  exact GeneratorReduction.append_mapped_triple DerivedCategory.Q
    (S.adjunction.unit.app (DerivedCategory.Q.obj T))
    ((coefficientSequenceLimit l E X).map
      ((pullbackTensorReductionModel l E X).hom.app ⟨T, hT⟩ ≫ DerivedCategory.Q.map ψ))
    (pullbackTensorLimitRoos l E X B).hom
    (((pullbackTensorOrdinaryAdjunction l E X).mapHomologicalComplex (.up ℤ)).homEquiv
      T B ψ)
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceRestriction l E X ⋙
        pullbackTensorConstantLimit l E X)) (.up ℤ)).inv.app B)
    (pullbackTensorRoosUnit l E X
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj B))
    (integralOperationsRoosMap (pullbackTensorTensorTower l E X P.obj Q.obj).hom)
    ((StrictTensorAugmentation.map l E X).app (P.obj, Q.obj)) ht hc

end WeilConjectures
