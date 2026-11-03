/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSingleTensorUnit

/-! # The unit of the specified supported single cup

Source: the singleton exterior product in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-single-cup-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity


private theorem transported_multiplication {C : Type*} [Category C]
    [MonoidalCategory C] {M : C} (e : M ≅ 𝟙_ C) :
    (tensorIso e e).hom ≫ (λ_ (𝟙_ C)).hom ≫ e.inv =
      e.hom ▷ M ≫ (λ_ M).hom := by
  simp only [tensorIso_hom, MonoidalCategory.tensorHom_def, Category.assoc]
  rw [leftUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem unit_restriction_tensor {C : Type*} [Category C] [MonoidalCategory C]
    {M M₀ N K : C} (q₀ : M ⟶ M₀) (u : M₀ ⟶ M) (q : M ⟶ N)
    (e : M ≅ 𝟙_ C) (t : N ⟶ K) (h : q₀ ≫ u = 𝟙 M) :
    (q₀ ⊗ₘ q) ≫ (u ▷ N ≫ e.hom ▷ N ≫ (λ_ N).hom ≫ t) =
      (e.hom ▷ M ≫ (λ_ M).hom) ≫ q ≫ t := by
  rw [← MonoidalCategory.tensorHom_id u, ← MonoidalCategory.tensorHom_id e.hom]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, h,
    Category.id_comp]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [leftUnitor_naturality_assoc]

private theorem coefficientMultiplication_unitor (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) :
    cupCoefficientMultiplication P X =
      (cupConstantIso P X).hom ▷ P.constant X ≫ (λ_ (P.constant X)).hom := by
  exact transported_multiplication (cupConstantIso P X)

private theorem left_unit_map_unique {C : Type*} [Category C] [MonoidalCategory C]
    {M M₀ N K : C} (q₀ : M ⟶ M₀) (u : M₀ ⟶ M) (q : M ⟶ N)
    (e : M ≅ 𝟙_ C) (t : N ⟶ K) (μ : M₀ ⊗ N ⟶ K)
    (m : M ⊗ M ⟶ M) (qK : M ⟶ K) [Epi (q₀ ⊗ₘ q)]
    (h₀ : q₀ ≫ u = 𝟙 M) (hm : m = e.hom ▷ M ≫ (λ_ M).hom)
    (ht : q ≫ t = qK) (hμ : (q₀ ⊗ₘ q) ≫ μ = m ≫ qK) :
    μ = u ▷ N ≫ e.hom ▷ N ≫ (λ_ N).hom ≫ t := by
  apply (cancel_epi (q₀ ⊗ₘ q)).mp
  rw [hμ, hm, ← ht]
  exact (unit_restriction_tensor q₀ u q e t h₀).symm

private theorem coefficientMap_left_unit (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    cupCoefficientMap P (𝟙 X) i =
      (lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app (P.constant X) ▷
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ≫
      (cupConstantIso P X).hom ▷
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ≫
      (λ_ ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z))).hom ≫
      P.functorialCupSupportMap true i (cupIntersection (𝟙 X) i)
        (pullback.snd (𝟙 X) i) pullback.condition.symm := by
  have : Epi (cupCoefficientRestriction P (𝟙 X)) := cupRestriction_epi P (𝟙 X)
  have : Epi (cupCoefficientRestriction P i) := cupRestriction_epi P i
  have : Epi (cupCoefficientRestriction P (𝟙 X) ▷ P.constant X) :=
    (tensorRight (P.constant X)).map_epi _
  have : Epi (((lowerStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 X)).obj
      (P.constant X)) ◁ cupCoefficientRestriction P i) := (tensorLeft _).map_epi _
  have : Epi (cupCoefficientRestriction P (𝟙 X) ⊗ₘ cupCoefficientRestriction P i) := by
    rw [MonoidalCategory.tensorHom_def]
    exact epi_comp _ _
  have hm : (cupCoefficientRestriction P (𝟙 X) ⊗ₘ cupCoefficientRestriction P i) ≫
      cupCoefficientMap P (𝟙 X) i = cupCoefficientMultiplication P X ≫
        cupCoefficientRestriction P (cupIntersection (𝟙 X) i) :=
    (cupCoefficientMap_existsUnique P (𝟙 X) i).exists.choose_spec
  have hr : cupCoefficientRestriction P i ≫
      P.functorialCupSupportMap true i (cupIntersection (𝟙 X) i)
        (pullback.snd (𝟙 X) i) pullback.condition.symm =
      cupCoefficientRestriction P (cupIntersection (𝟙 X) i) :=
    (P.functorialCupSupportMap_existsUnique true i (cupIntersection (𝟙 X) i)
      (pullback.snd (𝟙 X) i) pullback.condition.symm).choose_spec.1
  have hi : cupCoefficientRestriction P (𝟙 X) ≫
      (lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app (P.constant X) = 𝟙 _ := by
    rw [show cupCoefficientRestriction P (𝟙 X) =
      (lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).inv.app (P.constant X) from
        P.restriction_full true X]
    exact Iso.inv_hom_id_app _ _
  exact left_unit_map_unique _ _ _ (cupConstantIso P X) _ _ _ _ hi
    (coefficientMultiplication_unitor P X) hr hm

private theorem split_unit {C : Type*} [Category C] [MonoidalCategory C]
    {A U V K : C} (u : A ≅ U) (e : U ≅ 𝟙_ C) (t : V ⟶ K) :
    ((u ≪≫ e).hom ▷ V ≫ (λ_ V).hom) ≫ t =
      u.hom ▷ V ≫ e.hom ▷ V ≫ (λ_ V).hom ≫ t := by
  simp only [Iso.trans_hom, comp_whiskerRight, Category.assoc]

private theorem map_iso_unit_comp {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    {A U : C} (u : A ≅ U) (e : U ≅ 𝟙_ C) (d : F.obj (𝟙_ C) ≅ 𝟙_ D)
    {V K : D} (t : V ⟶ K) :
    (F.mapIso (u ≪≫ e) ≪≫ d).hom ▷ V ≫ (λ_ V).hom ≫ t =
      F.map u.hom ▷ V ≫ (F.mapIso e ≪≫ d).hom ▷ V ≫ (λ_ V).hom ≫ t := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    comp_whiskerRight, Category.assoc]

private theorem derived_coefficientMap_left_unit (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X) (hDM := cupMonoidal P X)
        (cupCoefficientMap P (𝟙 X) i) =
      (cupSingle P X).map
        ((lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app (P.constant X)) ▷
          (cupSingle P X).obj
            ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ≫
      ((cupSingle P X).mapIso (cupConstantIso P X) ≪≫
          DerivedCategory.singleFunctorObjUnitIso _).hom ▷
          (cupSingle P X).obj
            ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ≫
      (λ_ ((cupSingle P X).obj
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)))).hom ≫
      (cupSingle P X).map (P.functorialCupSupportMap true i (cupIntersection (𝟙 X) i)
        (pullback.snd (𝟙 X) i) pullback.condition.symm) := by
  let N := (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)
  let e : (lowerStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 X)).obj (P.constant X) ≅
      𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
    (lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app (P.constant X) ≪≫
      cupConstantIso P X
  have hc : cupCoefficientMap P (𝟙 X) i =
      (e.hom ▷ N ≫ (λ_ N).hom) ≫
        P.functorialCupSupportMap true i (cupIntersection (𝟙 X) i)
          (pullback.snd (𝟙 X) i) pullback.condition.symm := by
    exact (coefficientMap_left_unit P i).trans
      (split_unit ((lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app
        (P.constant X)) (cupConstantIso P X) _).symm
  have hu := coordinate_single_tensor_unit N e
  have hm := congrArg (fun z ↦ z ≫ (cupSingle P X).map
    (P.functorialCupSupportMap true i (cupIntersection (𝟙 X) i)
      (pullback.snd (𝟙 X) i) pullback.condition.symm)) hu
  have hs := map_iso_unit_comp (cupSingle P X)
    ((lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app (P.constant X))
    (cupConstantIso P X) (DerivedCategory.singleFunctorObjUnitIso _)
    ((cupSingle P X).map (P.functorialCupSupportMap true i
      (cupIntersection (𝟙 X) i) (pullback.snd (𝟙 X) i) pullback.condition.symm))
  unfold cupDerivedCoefficientMap
  rw [hc]
  erw [Functor.map_comp, ← Category.assoc]
  exact hm.trans ((Category.assoc _ _ _).trans hs)

private theorem inverse_unit_cup {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {A U N K T : C} (u : A ≅ U) (e : U ≅ 𝟙_ C) (β : N ⟶ T)
    (θ : A ⊗ N ⟶ K) [IsIso θ] (t : N ⟶ K)
    (hθ : θ = u.hom ▷ N ≫ e.hom ▷ N ≫ (λ_ N).hom ≫ t) :
    t ≫ inv θ ≫ (u.hom ⊗ₘ β) ≫ e.hom ▷ T ≫ (λ_ T).hom = β := by
  apply (cancel_epi (u.hom ▷ N ≫ e.hom ▷ N ≫ (λ_ N).hom)).mp
  calc
    (u.hom ▷ N ≫ e.hom ▷ N ≫ (λ_ N).hom) ≫
        (t ≫ inv θ ≫ (u.hom ⊗ₘ β) ≫ e.hom ▷ T ≫ (λ_ T).hom) =
      θ ≫ inv θ ≫ (u.hom ⊗ₘ β) ≫ e.hom ▷ T ≫ (λ_ T).hom := by
        simpa only [Category.assoc] using congrArg
          (fun a ↦ a ≫ inv θ ≫ (u.hom ⊗ₘ β) ≫ e.hom ▷ T ≫ (λ_ T).hom) hθ.symm
    _ = (u.hom ⊗ₘ β) ≫ e.hom ▷ T ≫ (λ_ T).hom := by
      rw [IsIso.hom_inv_id_assoc]
    _ = (u.hom ▷ N ≫ e.hom ▷ N ≫ (λ_ N).hom) ≫ β := by
      rw [← tensorHom_id e.hom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
      simp only [MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc]
      rw [leftUnitor_naturality]

/-- The empty left factor of the specified supported cup is its canonical unit.

Source: the singleton exterior product in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-single-cup-unit).

Proof: the restriction maps to closed constant coefficients are epic, and tensor
preserves epimorphisms. Their defining multiplication square identifies the
underived cup with the ordinary left unitor and the canonical change of support.
The proved single-tensor unit equation lifts this formula to the derived cup.
Cancel the invertible derived coefficient map and the invertible left unitor.
Naturality of the unitor in the remaining arrow then gives the stated equality. -/
theorem coordinate_single_cup_unit (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (K : CupDerivedCategory P X)
    (β : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ K) :
    (cupSingle P X).map (P.functorialCupSupportMap true i (cupIntersection (𝟙 X) i)
        (pullback.snd (𝟙 X) i) pullback.condition.symm) ≫
      @inv (CupDerivedCategory P X) _ _ _
        (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
          (hDM := cupMonoidal P X) (cupCoefficientMap P (𝟙 X) i))
        (cupDerivedCoefficientMap_isIso P (𝟙 X) i) ≫
      ((cupSingle P X).map
        ((lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app (P.constant X)) ⊗ₘ β) ≫
      ((cupSingle P X).mapIso (cupConstantIso P X) ≪≫
          DerivedCategory.singleFunctorObjUnitIso _).hom ▷ K ≫ (λ_ K).hom = β := by
  let u := (cupSingle P X).mapIso
    ((lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app (P.constant X))
  let e := (cupSingle P X).mapIso (cupConstantIso P X) ≪≫
    DerivedCategory.singleFunctorObjUnitIso _
  let μ := cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
    (hDM := cupMonoidal P X) (cupCoefficientMap P (𝟙 X) i)
  exact @inverse_unit_cup (CupDerivedCategory P X) _ (cupMonoidal P X)
    _ _ _ _ _ u e β μ (cupDerivedCoefficientMap_isIso P (𝟙 X) i) _
      (derived_coefficientMap_left_unit P i)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
