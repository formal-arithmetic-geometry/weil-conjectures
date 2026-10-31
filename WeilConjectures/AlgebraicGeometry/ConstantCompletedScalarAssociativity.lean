/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarLimitReduction
import WeilConjectures.AlgebraicGeometry.CompletedScalarAssociatorLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Associativity of the constant-to-completed scalar comparison

Source: Stacks 03EK, 06YY and 07A6; strict scalar composition, auxiliary Step 9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
private theorem transport_scalar_square
    {D₀ D₁ D₂ C₀ C₁ C₂ : Type*}
    [Category D₀] [Category D₁] [Category D₂]
    [Category C₀] [Category C₁] [Category C₂]
    {U₀ : D₀ ⥤ C₀} {U₁ : D₁ ⥤ C₁} {U₂ : D₂ ⥤ C₂}
    {A₁₀ X₁₀ : D₀ ⥤ D₁} {A₂₁ X₂₁ : D₁ ⥤ D₂}
    {A₂₀ X₂₀ : D₀ ⥤ D₂}
    {B₁₀ : C₀ ⥤ C₁} {B₂₁ : C₁ ⥤ C₂} {B₂₀ : C₀ ⥤ C₂}
    (χ₁₀ : U₀ ⋙ B₁₀ ≅ A₁₀ ⋙ U₁) (χ₂₁ : U₁ ⋙ B₂₁ ≅ A₂₁ ⋙ U₂)
    (χ₂₀ : U₀ ⋙ B₂₀ ≅ A₂₀ ⋙ U₂)
    (δ₁₀ : U₀ ⋙ B₁₀ ≅ X₁₀ ⋙ U₁) (δ₂₁ : U₁ ⋙ B₂₁ ≅ X₂₁ ⋙ U₂)
    (δ₂₀ : U₀ ⋙ B₂₀ ≅ X₂₀ ⋙ U₂)
    (m₁₀ : A₁₀ ≅ X₁₀) (m₂₁ : A₂₁ ≅ X₂₁) (m₂₀ : A₂₀ ≅ X₂₀)
    (αA : A₁₀ ⋙ A₂₁ ≅ A₂₀) (αX : X₁₀ ⋙ X₂₁ ≅ X₂₀)
    (αB : B₁₀ ⋙ B₂₁ ≅ B₂₀)
    (h₁₀ : χ₁₀ ≪≫ isoWhiskerRight m₁₀ U₁ = δ₁₀)
    (h₂₁ : χ₂₁ ≪≫ isoWhiskerRight m₂₁ U₂ = δ₂₁)
    (h₂₀ : χ₂₀ ≪≫ isoWhiskerRight m₂₀ U₂ = δ₂₀)
    (hα : ∀ K, αA.hom.app K ≫ m₂₀.hom.app K =
      A₂₁.map (m₁₀.hom.app K) ≫ m₂₁.hom.app (X₁₀.obj K) ≫ αX.hom.app K)
    (hδ : ∀ K, B₂₁.map (δ₁₀.hom.app K) ≫ δ₂₁.hom.app (X₁₀.obj K) ≫
      U₂.map (αX.hom.app K) = αB.hom.app (U₀.obj K) ≫ δ₂₀.hom.app K)
    (K : D₀) :
    B₂₁.map (χ₁₀.hom.app K) ≫ χ₂₁.hom.app (A₁₀.obj K) ≫
      U₂.map (αA.hom.app K) = αB.hom.app (U₀.obj K) ≫ χ₂₀.hom.app K := by
  have h₁₀' := congrArg (fun e ↦ e.hom.app K) h₁₀
  have h₂₁' := congrArg (fun e ↦ e.hom.app (X₁₀.obj K)) h₂₁
  have h₂₀' := congrArg (fun e ↦ e.hom.app K) h₂₀
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app] at h₁₀' h₂₁' h₂₀'
  apply (cancel_mono (U₂.map (m₂₀.hom.app K))).mp
  simp only [Category.assoc]
  rw [← U₂.map_comp, hα]
  simp only [Functor.map_comp]
  rw [← reassoc_of% χ₂₁.hom.naturality (m₁₀.hom.app K), reassoc_of% h₂₁']
  have hm := congrArg B₂₁.map h₁₀'
  simp only [Functor.map_comp] at hm
  rw [reassoc_of% hm, hδ, h₂₀']

private theorem localize_scalar_square
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂]
    [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
    {U₀ : A₀ ⥤ B₀} {U₁ : A₁ ⥤ B₁} {U₂ : A₂ ⥤ B₂}
    {X₁₀ : A₀ ⥤ A₁} {X₂₁ : A₁ ⥤ A₂} {X₂₀ : A₀ ⥤ A₂}
    {Y₁₀ : B₀ ⥤ B₁} {Y₂₁ : B₁ ⥤ B₂} {Y₂₀ : B₀ ⥤ B₂}
    [U₀.Additive] [U₁.Additive] [U₂.Additive]
    [X₁₀.Additive] [X₂₁.Additive] [X₂₀.Additive]
    [Y₁₀.Additive] [Y₂₁.Additive] [Y₂₀.Additive]
    [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    [PreservesFiniteLimits X₁₀] [PreservesFiniteColimits X₁₀]
    [PreservesFiniteLimits X₂₁] [PreservesFiniteColimits X₂₁]
    [PreservesFiniteLimits X₂₀] [PreservesFiniteColimits X₂₀]
    [PreservesFiniteLimits Y₁₀] [PreservesFiniteColimits Y₁₀]
    [PreservesFiniteLimits Y₂₁] [PreservesFiniteColimits Y₂₁]
    [PreservesFiniteLimits Y₂₀] [PreservesFiniteColimits Y₂₀]
    (δ₁₀ : U₀ ⋙ Y₁₀ ≅ X₁₀ ⋙ U₁) (δ₂₁ : U₁ ⋙ Y₂₁ ≅ X₂₁ ⋙ U₂)
    (δ₂₀ : U₀ ⋙ Y₂₀ ≅ X₂₀ ⋙ U₂)
    (αX : X₁₀ ⋙ X₂₁ ≅ X₂₀) (αY : Y₁₀ ⋙ Y₂₁ ≅ Y₂₀)
    (hδ : ∀ M, Y₂₁.map (δ₁₀.hom.app M) ≫ δ₂₁.hom.app (X₁₀.obj M) ≫
      U₂.map (αX.hom.app M) = αY.hom.app (U₀.obj M) ≫ δ₂₀.hom.app M)
    (K : DerivedCategory A₀) :
    Y₂₁.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso δ₁₀).hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso δ₂₁).hom.app (X₁₀.mapDerivedCategory.obj K) ≫
      U₂.mapDerivedCategory.map (((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso αX).hom.app K) =
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso αY).hom.app (U₀.mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategorySquareIso δ₂₀).hom.app K := by
  have hh := Functor.mapDerivedCategorySquareIso_hom_app_comp δ₁₀ δ₂₁ δ₂₀
    αY.symm αX.symm (fun M ↦ ?_) K
  · have hx : Functor.mapDerivedCategoryTriangleIso αX.symm =
        ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryNatIso αX).symm := by
      apply Iso.ext
      simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
        Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm]
    have hy : Functor.mapDerivedCategoryTriangleIso αY.symm =
        ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryNatIso αY).symm := by
      apply Iso.ext
      simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
        Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm]
    rw [hx, hy] at hh
    simp only [Iso.symm_hom] at hh
    apply (cancel_epi (((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso αY).inv.app (U₀.mapDerivedCategory.obj K))).mp
    apply (cancel_mono (U₂.mapDerivedCategory.map
      (((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso αX).inv.app K))).mp
    simp only [Category.assoc]
    rw [← U₂.mapDerivedCategory.map_comp, Iso.hom_inv_id_app]
    erw [U₂.mapDerivedCategory.map_id, Category.comp_id]
    rw [← hh]
    simp only [Iso.inv_hom_id_app_assoc]
  · apply (Iso.eq_inv_comp (αY.app (U₀.obj M))).2
    apply (cancel_mono (U₂.map (αX.hom.app M))).mp
    simp only [Category.assoc]
    simp only [Iso.symm_hom]
    rw [← U₂.map_comp, Iso.inv_hom_id_app]
    erw [U₂.map_id, Category.comp_id]
    exact (hδ M).symm

namespace WeilConjectures.PurStrictScalar

/-- Constant-to-completed balancing preserves the ordinary tensor associator.
Source: Stacks 03EK, 06YY and 07A6; auxiliary Step 9 of strict scalar composition
(blueprint: lem-pur-constant-completed-scalar-associativity).

Proof: work first with ordinary module sheaves. On a local double pure tensor
((x tensor b) tensor c), both routes send the two constant scalars to their
completed images and multiply c by the image of b. The constant-to-completed
coefficient squares commute, so the two products agree. The tensor universal
property and sheafification give equality of the ordinary maps. The ordinary
associator used here is the left-adjoint-uniqueness comparison: transpose its
pure-tensor formula under the two scalar adjunctions; it carries the successive
units to the direct unit, which characterizes that comparison uniquely.
Now choose a flat-term K-flat representative of the input. All constant scalar
extensions are exact by finite freeness; completed scalar extensions preserve
these representatives. Apply the ordinary equation degreewise and localize.
The defining complex-counit normalization of scalarCompletion identifies its
three occurrences with these localized balancing maps. The same successive-unit
calculation identifies the localized associator with tensorComposition for the
completed scalar adjunctions. Cancel the invertible computation counits. This
gives the displayed equation on every object of the unbounded derived category.
Zero objects, identity embeddings and the empty site obey the same pure-tensor
and unit formulas; no constructibility or completeness assumption is needed. -/
theorem scalarCompletion_composition
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (j : F →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (baseTensor l F L j W).map ((scalarCompletion l E F i W).hom.app K) ≫
        (scalarCompletion l F L j W).hom.app
          ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj K) ≫
        (scalarConstantRestriction l L W).map
          ((PurCompactSupport.tensorComposition _ _ _
            (PurCompactSupport.completedMap_composition l E F i L j W)).hom.app K) =
      (letI := (baseTensor_exact l E F i W).1
       letI := (baseTensor_exact l E F i W).2
       letI := (baseTensor_exact l F L j W).1
       letI := (baseTensor_exact l F L j W).2
       letI := (baseTensor_exact l E L (j.comp i) W).1
       letI := (baseTensor_exact l E L (j.comp i) W).2
       ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((((pbcScalarAdjunction (constantMap l E F i W)).comp
            (pbcScalarAdjunction (constantMap l F L j W))).ofNatIsoRight
              (pbcRestrictComp _ _ _ (by
                unfold constantMap
                rw [← Functor.map_comp]
                congr 1))).leftAdjointUniq
                  (pbcScalarAdjunction (constantMap l E L (j.comp i) W)))).hom.app
          ((scalarConstantRestriction l E W).obj K)) ≫
        (scalarCompletion l E L (j.comp i) W).hom.app K := by
  have := (baseTensor_exact l E F i W).1
  have := (baseTensor_exact l E F i W).2
  have := (baseTensor_exact l F L j W).1
  have := (baseTensor_exact l F L j W).2
  have := (baseTensor_exact l E L (j.comp i) W).1
  have := (baseTensor_exact l E L (j.comp i) W).2
  have := (completedTensor_exact l E F i W).1
  have := (completedTensor_exact l E F i W).2
  have := (completedTensor_exact l F L j W).1
  have := (completedTensor_exact l F L j W).2
  have := (completedTensor_exact l E L (j.comp i) W).1
  have := (completedTensor_exact l E L (j.comp i) W).2
  have := pbcExtend_additive (completedCoefficientMap l E F i W)
  have := pbcExtend_additive (completedCoefficientMap l F L j W)
  have := pbcExtend_additive (completedCoefficientMap l E L (j.comp i) W)
  have := scalarConstantRestriction_limits l E W
  have := scalarConstantRestriction_colimits l E W
  have := scalarConstantRestriction_limits l F W
  have := scalarConstantRestriction_colimits l F W
  have := scalarConstantRestriction_limits l L W
  have := scalarConstantRestriction_colimits l L W
  let αX := ordinaryScalarAssociator _ _ _
    (PurCompactSupport.completedMap_composition l E F i L j W)
  let αY := ordinaryScalarAssociator _ _ _ (show
    constantMap l E F i W ≫ constantMap l F L j W =
      constantMap l E L (j.comp i) W by
    unfold constantMap
    rw [← Functor.map_comp]
    congr 1)
  have hδ := localize_scalar_square
    (scalarCompletionOrdinary l E F i W)
    (scalarCompletionOrdinary l F L j W)
    (scalarCompletionOrdinary l E L (j.comp i) W) αX αY
    (scalarCompletionOrdinary_composition l E F i L j W)
  exact transport_scalar_square
    (scalarCompletion l E F i W) (scalarCompletion l F L j W)
    (scalarCompletion l E L (j.comp i) W)
    (Functor.mapDerivedCategorySquareIso (scalarCompletionOrdinary l E F i W))
    (Functor.mapDerivedCategorySquareIso (scalarCompletionOrdinary l F L j W))
    (Functor.mapDerivedCategorySquareIso (scalarCompletionOrdinary l E L (j.comp i) W))
    (completedTensorModel l E F i W) (completedTensorModel l F L j W)
    (completedTensorModel l E L (j.comp i) W)
    (PurCompactSupport.tensorComposition _ _ _
      (PurCompactSupport.completedMap_composition l E F i L j W))
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso αX)
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso αY)
    (scalarCompletion_exactModel l E F i W) (scalarCompletion_exactModel l F L j W)
    (scalarCompletion_exactModel l E L (j.comp i) W)
    (completedTensorModel_composition l E F i L j W) hδ K

end WeilConjectures.PurStrictScalar
