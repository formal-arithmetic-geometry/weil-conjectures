/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap

/-! # Cancellation of the zero shifts in a supported binary cup

Source: the supported cup composite, at cohomological degrees zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v w
open CategoryTheory MonoidalCategory AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

private theorem zero_shift_tensor {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [HasShift C ℤ]
    [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    {L M F G : C} (α : L ⟶ F) (β : M ⟶ G) :
    ((α ≫ (shiftFunctorZero C ℤ).inv.app F) ⊗ₘ
      (β ≫ (shiftFunctorZero C ℤ).inv.app G)) ≫
        (cupTensorShiftIso F G 0 0).hom ≫
          (shiftFunctorZero C ℤ).hom.app (F ⊗ G) = α ⊗ₘ β := by
  simp only [cupTensorShiftIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.commShiftIso_zero,
    Functor.CommShift.isoZero_hom_app, shiftFunctorAdd_zero_add_inv_app,
    eqToHom_refl, Category.comp_id, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [← (shiftFunctorZero C ℤ).inv.naturality_assoc]
  dsimp only [Functor.id_map, Functor.id_obj, curriedTensor_obj_obj,
    curriedTensor_obj_map, Functor.flip_obj_map, curriedTensor_map_app]
  simp only [Category.comp_id]
  simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [Functor.id_obj, Functor.flip_obj_obj, curriedTensor_obj_obj]
  simp only [Category.comp_id, Iso.inv_hom_id_app]
  simp only [Category.id_comp]
  change (α ≫ (shiftFunctorZero C ℤ).inv.app F ≫
      (shiftFunctorZero C ℤ).hom.app F ⊗ₘ β) ≫ 𝟙 (F ⊗ G) = α ⊗ₘ β
  simp

/-- The inverse coefficient tensor comparison followed by the tensor of two inputs.
Source: the supported cup composite, with both cohomological degrees zero.
(blueprint: lem-pur-coordinate-zero-cup-tensor). -/
def zeroCupTensor (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (α : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ F.obj)
    (β : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W)) ⟶ G.obj) :
    (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
        (P.constant (CategoryTheory.Limits.pullback i j))) ⟶
      cupTensorObject P X F.obj G.obj :=
  @inv (CupDerivedCategory P X) _ _ _
      (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
        (hDM := cupMonoidal P X) (cupCoefficientMap P i j))
      (cupDerivedCoefficientMap_isIso P i j) ≫
    @MonoidalCategory.tensorHom (CupDerivedCategory P X) _
      (cupMonoidal P X).toMonoidalCategoryStruct _ _ _ _ α β

/-- The existing zero-degree supported cup is literally the unshifted tensor composite.
Source: def-pur-supported-cup and the definition of cupZero.
(blueprint: lem-pur-coordinate-zero-cup-tensor).
Proof: expand the two zero commutation isomorphisms using the commShiftIso_zero
identity, and the additive shift isomorphism using shiftFunctorAdd_zero_add. The
naturality of shiftFunctorZero moves its inverse through the shifted map.
Cancel the inverse pairs and combine tensor maps by bifunctoriality. The
coefficient comparison is the common first map and remains unchanged. -/
theorem cupZero_tensor (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (j : W ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (α : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ F.obj)
    (β : (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W)) ⟶ G.obj) :
    cupZero P aX i j F G α β = zeroCupTensor P i j F G α β := by
  unfold cupZero supportedCup cupComposite zeroCupTensor
  simp only [Category.assoc]
  congr 1
  exact zero_shift_tensor α β

end AlgebraicGeometry.ProEtale.AffineZeroPurity
