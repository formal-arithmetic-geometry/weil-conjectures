/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidalShift
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-!
# Comparisons with derived tensor products commuting with shifts

* For a K-flat `X`, the counits `tensorLeftCounit X` and `tensorRightCounit X` of the derived
  tensor product with `Qh X` commute with the shifts.
* `DerivedCategory.commShift_of_tensorLeft_fac`, `DerivedCategory.commShift_of_tensorRight_fac`:
  a natural transformation `LF(Qh X ⊗ᴸ -) ⟶ LF(Qh X) ⊗ᴸ LF(-)` (or with the variables swapped)
  which is compatible on the homotopy category with the oplax monoidal structure of an additive
  functor `F` commutes with the shifts.
-/

@[expose] public section

universe w v

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace DerivedCategory

section

variable (C : Type*) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

local instance hasColimitsOfSize_tensorCounitShift : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

variable {C}

lemma commShift_tensorLeftCounit
    (X : HomotopyCategory C (.up ℤ)) (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X) :
    NatTrans.CommShift (tensorLeftCounit X) ℤ := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hP := (HomotopyCategory.kFlat_quotient_obj_iff _).1 hX
  have e := commShiftTensorLeft_eq C ⟨P, hP⟩
  let := commShiftTensorLeftQhObj ((HomotopyCategory.quotient C _).obj P) hX
  have := isIso_tensorLeftCounit ((HomotopyCategory.quotient C _).obj P) hX
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).obj ((HomotopyCategory.quotient C _).obj P) ⋙ Qh)
      ((curriedTensor _).obj (Qh.obj ((HomotopyCategory.quotient C _).obj P))) :=
    ⟨asIso (tensorLeftCounit _)⟩
  have h := NatTrans.commShift_iso_hom_of_localization Qh (HomotopyCategory.quasiIso C (.up ℤ)) ℤ
    ((curriedTensor _).obj ((HomotopyCategory.quotient C _).obj P) ⋙ Qh)
    ((curriedTensor (DerivedCategory C)).obj
      (Qh.obj ((HomotopyCategory.quotient C _).obj P)))
  convert h using 1
  · rfl
  · congr 1

lemma commShift_tensorRightCounit
    (X : HomotopyCategory C (.up ℤ)) (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X) :
    NatTrans.CommShift (tensorRightCounit X) ℤ := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hP := (HomotopyCategory.kFlat_quotient_obj_iff _).1 hX
  have e := commShiftTensorRight_eq C ⟨P, hP⟩
  let := commShiftTensorRightQhObj ((HomotopyCategory.quotient C _).obj P) hX
  have := isIso_tensorRightCounit ((HomotopyCategory.quotient C _).obj P) hX
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj ((HomotopyCategory.quotient C _).obj P) ⋙ Qh)
      ((curriedTensor _).flip.obj (Qh.obj ((HomotopyCategory.quotient C _).obj P))) :=
    ⟨asIso (tensorRightCounit _)⟩
  have h := NatTrans.commShift_iso_hom_of_localization Qh (HomotopyCategory.quasiIso C (.up ℤ)) ℤ
    ((curriedTensor _).flip.obj ((HomotopyCategory.quotient C _).obj P) ⋙ Qh)
    ((curriedTensor (DerivedCategory C)).flip.obj
      (Qh.obj ((HomotopyCategory.quotient C _).obj P)))
  convert h using 1
  · rfl
  · congr 1

end


section Comparison

variable {C₁ C₂ : Type*} [Category.{v} C₁] [Abelian C₁] [IsGrothendieckAbelian.{w} C₁]
  [HasDerivedCategory.{w} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁] [MonoidalPreadditive C₁]
  [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
  [Category.{v} C₂] [Abelian C₂] [IsGrothendieckAbelian.{w} C₂]
  [HasDerivedCategory.{w} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂] [MonoidalPreadditive C₂]
  [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]

local instance hasColimitsOfSize_comparisonShift₁ : HasColimitsOfSize.{0, 0} C₁ :=
  hasColimitsOfSizeShrink C₁
local instance hasColimitsOfSize_comparisonShift₂ : HasColimitsOfSize.{0, 0} C₂ :=
  hasColimitsOfSizeShrink C₂

variable (F : C₁ ⥤ C₂) [F.Additive] [F.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
  (LF : DerivedCategory C₁ ⥤ DerivedCategory C₂) [LF.CommShift ℤ]
  (cL : Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ Qh) [IsIso cL] [NatTrans.CommShift cL ℤ]

set_option trace.profiler true in
open Functor in
/-- A natural transformation `τ : LF(Qh X ⊗ᴸ -) ⟶ LF(Qh X) ⊗ᴸ LF(-)` which is compatible, on
the homotopy category, with the comparison `F(X ⊗ -) ⟶ F(X) ⊗ F(-)`, commutes with the shifts,
if `X` and `F(X)` are K-flat. -/
lemma commShift_of_tensorLeft_fac (X : HomotopyCategory C₁ (.up ℤ))
    (hX : (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat X)
    (hFX : (HomotopyCategory.quasiIso C₂ (.up ℤ)).kFlat ((F.mapHomotopyCategory (.up ℤ)).obj X))
    (τ : (curriedTensor (DerivedCategory C₁)).obj (Qh.obj X) ⋙ LF ⟶
      LF ⋙ (curriedTensor (DerivedCategory C₂)).obj (LF.obj (Qh.obj X)))
    (hτ : ∀ M, τ.app (Qh.obj M) ≫ cL.app X ▷ LF.obj (Qh.obj M) ≫
        Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj X) ◁ cL.app M ≫
        (tensorLeftCounit ((F.mapHomotopyCategory (.up ℤ)).obj X)).app
          ((F.mapHomotopyCategory (.up ℤ)).obj M) =
      LF.map ((tensorLeftCounit X).app M) ≫ cL.app (X ⊗ M) ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app X).app M)) :
    NatTrans.CommShift τ ℤ := by
  have : HasCoproducts.{0} C₁ := inferInstance
  have : HasCoproducts.{0} C₂ := inferInstance
  let : MonoidalCategory (DerivedCategory C₁) :=
    monoidalCategoryOfMonoidalClosedBraidedCategory C₁
  let : MonoidalCategory (DerivedCategory C₂) :=
    monoidalCategoryOfMonoidalClosedBraidedCategory C₂
  let G := F.mapHomotopyCategory (.up ℤ)
  let c₂ : Qh ⋙ ((curriedTensor (DerivedCategory C₁)).obj (Qh.obj X) ⋙ LF) ⟶
      ((curriedTensor (HomotopyCategory C₁ (.up ℤ))).obj X ⋙ G) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (tensorLeftCounit X) LF ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ((curriedTensor (HomotopyCategory C₁ (.up ℤ))).obj X) cL ≫
      (Functor.associator _ _ _).inv
  let δ₀ : ((curriedTensor (HomotopyCategory C₁ (.up ℤ))).obj X ⋙ G) ⋙ Qh ⟶ (G ⋙ (curriedTensor (HomotopyCategory C₂ (.up ℤ))).obj (G.obj X)) ⋙ Qh :=
    Functor.whiskerRight (G := (curriedTensor (HomotopyCategory C₁ (.up ℤ))).obj X ⋙ G)
      (H := G ⋙ (curriedTensor (HomotopyCategory C₂ (.up ℤ))).obj (G.obj X))
      ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app X) Qh
  let c₁ : Qh ⋙ (LF ⋙ (curriedTensor (DerivedCategory C₂)).obj (LF.obj (Qh.obj X))) ⟶
      (G ⋙ (curriedTensor (HomotopyCategory C₂ (.up ℤ))).obj (G.obj X)) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerLeft (Qh ⋙ LF) ((curriedTensor (DerivedCategory C₂)).map (cL.app X)) ≫
      Functor.whiskerRight cL ((curriedTensor (DerivedCategory C₂)).obj (Qh.obj (G.obj X))) ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft G (tensorLeftCounit (G.obj X)) ≫
      (Functor.associator _ _ _).inv
  have := isIso_tensorLeftCounit (G.obj X) hFX
  have : IsIso c₁ := by dsimp only [c₁]; infer_instance
  have fac : Functor.whiskerLeft Qh τ ≫ c₁ = c₂ ≫ δ₀ := by
    ext M
    simpa only [c₁, c₂, δ₀, G, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.comp_obj, curriedTensor_obj_obj, curriedTensor_obj_map, curriedTensor_map_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc] using hτ M
  have := commShift_tensorLeftCounit X hX
  have := commShift_tensorLeftCounit (G.obj X) hFX
  have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
  have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
  have := OplaxMonoidal.commShift_mapHomotopyCategoryδNatTrans_app F X
  have : NatTrans.CommShift δ₀ ℤ :=
    NatTrans.CommShift.whiskerRight (F₁ := (curriedTensor (HomotopyCategory C₁ (.up ℤ))).obj X ⋙ G)
      (F₂ := G ⋙ (curriedTensor (HomotopyCategory C₂ (.up ℤ))).obj (G.obj X)) _ Qh ℤ
  have : NatTrans.CommShift (inv c₁) ℤ := NatTrans.CommShift.of_isIso c₁ ℤ
  have : NatTrans.CommShift (whiskerLeft Qh τ) ℤ := by
    rw [(IsIso.eq_comp_inv c₁).2 fac]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ Qh
    (fun M ↦ ⟨Qh.objPreimage M, (Qh.objObjPreimageIso M).inv, inferInstance⟩)

set_option trace.profiler true in
open Functor in
/-- A natural transformation `τ : LF(- ⊗ᴸ Qh X) ⟶ LF(-) ⊗ᴸ LF(Qh X)` which is compatible, on
the homotopy category, with the comparison `F(- ⊗ X) ⟶ F(-) ⊗ F(X)`, commutes with the shifts,
if `X` and `F(X)` are K-flat. -/
lemma commShift_of_tensorRight_fac (X : HomotopyCategory C₁ (.up ℤ))
    (hX : (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat X)
    (hFX : (HomotopyCategory.quasiIso C₂ (.up ℤ)).kFlat ((F.mapHomotopyCategory (.up ℤ)).obj X))
    (τ : (curriedTensor (DerivedCategory C₁)).flip.obj (Qh.obj X) ⋙ LF ⟶
      LF ⋙ (curriedTensor (DerivedCategory C₂)).flip.obj (LF.obj (Qh.obj X)))
    (hτ : ∀ M, τ.app (Qh.obj M) ≫ cL.app M ▷ LF.obj (Qh.obj X) ≫
        Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj M) ◁ cL.app X ≫
        (tensorRightCounit ((F.mapHomotopyCategory (.up ℤ)).obj X)).app
          ((F.mapHomotopyCategory (.up ℤ)).obj M) =
      LF.map ((tensorRightCounit X).app M) ≫ cL.app (M ⊗ X) ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app M).app X)) :
    NatTrans.CommShift τ ℤ := by
  have : HasCoproducts.{0} C₁ := inferInstance
  have : HasCoproducts.{0} C₂ := inferInstance
  let : MonoidalCategory (DerivedCategory C₁) :=
    monoidalCategoryOfMonoidalClosedBraidedCategory C₁
  let : MonoidalCategory (DerivedCategory C₂) :=
    monoidalCategoryOfMonoidalClosedBraidedCategory C₂
  let G := F.mapHomotopyCategory (.up ℤ)
  let c₂ : Qh ⋙ ((curriedTensor (DerivedCategory C₁)).flip.obj (Qh.obj X) ⋙ LF) ⟶
      ((curriedTensor (HomotopyCategory C₁ (.up ℤ))).flip.obj X ⋙ G) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (tensorRightCounit X) LF ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ((curriedTensor (HomotopyCategory C₁ (.up ℤ))).flip.obj X) cL ≫
      (Functor.associator _ _ _).inv
  let δ₀ : ((curriedTensor (HomotopyCategory C₁ (.up ℤ))).flip.obj X ⋙ G) ⋙ Qh ⟶
      (G ⋙ (curriedTensor (HomotopyCategory C₂ (.up ℤ))).flip.obj (G.obj X)) ⋙ Qh :=
    Functor.whiskerRight (G := (curriedTensor (HomotopyCategory C₁ (.up ℤ))).flip.obj X ⋙ G)
      (H := G ⋙ (curriedTensor (HomotopyCategory C₂ (.up ℤ))).flip.obj (G.obj X))
      ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).flipApp X) Qh
  let c₁ : Qh ⋙ (LF ⋙ (curriedTensor (DerivedCategory C₂)).flip.obj (LF.obj (Qh.obj X))) ⟶
      (G ⋙ (curriedTensor (HomotopyCategory C₂ (.up ℤ))).flip.obj (G.obj X)) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight cL ((curriedTensor (DerivedCategory C₂)).flip.obj (LF.obj (Qh.obj X))) ≫
      Functor.whiskerLeft (G ⋙ Qh) ((curriedTensor (DerivedCategory C₂)).flip.map (cL.app X)) ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft G (tensorRightCounit (G.obj X)) ≫
      (Functor.associator _ _ _).inv
  have := isIso_tensorRightCounit (G.obj X) hFX
  have : IsIso c₁ := by dsimp only [c₁]; infer_instance
  have fac : Functor.whiskerLeft Qh τ ≫ c₁ = c₂ ≫ δ₀ := by
    ext M
    simpa only [c₁, c₂, δ₀, G, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.comp_obj, Functor.flip_obj_obj, Functor.flip_obj_map, Functor.flip_map_app,
      NatTrans.flipApp, flipFunctor_map_app_app, curriedTensor_obj_obj, curriedTensor_obj_map,
      curriedTensor_map_app,
      associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc] using hτ M
  have := commShift_tensorRightCounit X hX
  have := commShift_tensorRightCounit (G.obj X) hFX
  have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
  have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
  have := OplaxMonoidal.commShift_mapHomotopyCategoryδNatTrans_flipApp F X
  have : NatTrans.CommShift δ₀ ℤ :=
    NatTrans.CommShift.whiskerRight (F₁ := (curriedTensor (HomotopyCategory C₁ (.up ℤ))).flip.obj X ⋙ G)
      (F₂ := G ⋙ (curriedTensor (HomotopyCategory C₂ (.up ℤ))).flip.obj (G.obj X)) _ Qh ℤ
  have : NatTrans.CommShift (inv c₁) ℤ := NatTrans.CommShift.of_isIso c₁ ℤ
  have : NatTrans.CommShift (whiskerLeft Qh τ) ℤ := by
    rw [(IsIso.eq_comp_inv c₁).2 fac]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ Qh
    (fun M ↦ ⟨Qh.objPreimage M, (Qh.objObjPreimageIso M).inv, inferInstance⟩)

end Comparison
end DerivedCategory
