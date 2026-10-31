/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction

/-!
# Tensor comparisons of non-exact left derived functors commute with shifts

`DerivedCategory.commShift_of_tensorLeft_fac` shows that a natural transformation
`LF(Qh X ⊗ᴸ -) ⟶ LF(Qh X) ⊗ᴸ LF(-)` compatible on the homotopy category with the comonoidal
structure of `F` commutes with the shifts, when the counit `Qh ⋙ LF ⟶ K(F) ⋙ Qh` is an
isomorphism (for instance for `F` exact). We remove this hypothesis: it suffices that the counit
is an isomorphism on K-flat complexes, as for the total left derived functor of a functor
preserving quasi-isomorphisms between K-flat complexes
(`DerivedCategory.commShift_of_tensorLeft_fac_of_kFlat`,
`DerivedCategory.commShift_of_tensorRight_fac_of_kFlat`).

The criterion is `CategoryTheory.NatTrans.CommShift.of_whiskerLeft_comp`: a natural
transformation `τ` commutes with the shifts as soon as `L ◁ τ ≫ c` does, for a transformation
`c` commuting with the shifts which is an isomorphism on enough objects.
-/

@[expose] public section

universe w v

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.NatTrans.CommShift

variable {C D E G : Type*} [Category* C] [Category* D] [Category* E] [Category* G] {A : Type*}
  [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A] [HasShift G A]
  {F₁ F₂ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.CommShift A] [F₂.CommShift A]

/-- A natural transformation `τ : F₁ ⟶ F₂` commutes with shifts if `L ◁ τ ≫ c` does, for a
functor `L` and a natural transformation `c : L ⋙ F₂ ⟶ H` commuting with shifts, provided every
object `X` maps to an object `L.obj Y` by a morphism `f` such that `F₂.map f` and `c.app Y` are
isomorphisms. -/
lemma of_whiskerLeft_comp (L : E ⥤ C) [L.CommShift A] {H : E ⥤ D} [H.CommShift A]
    (c : L ⋙ F₂ ⟶ H) [NatTrans.CommShift c A]
    [NatTrans.CommShift (Functor.whiskerLeft L τ ≫ c) A]
    (h : ∀ X, ∃ (Y : E) (f : X ⟶ L.obj Y), IsIso (F₂.map f) ∧ IsIso (c.app Y)) :
    NatTrans.CommShift τ A where
  shift_comm a := by
    ext X
    obtain ⟨Y, f, hf, hc⟩ := h X
    have hY : (F₁.commShiftIso a).hom.app (L.obj Y) ≫ (τ.app (L.obj Y))⟦a⟧' =
        τ.app ((L.obj Y)⟦a⟧) ≫ (F₂.commShiftIso a).hom.app (L.obj Y) := by
      have h₁ := NatTrans.shift_app_comm (Functor.whiskerLeft L τ ≫ c) a Y
      have h₂ := NatTrans.shift_app_comm c a Y
      simp only [Functor.comp_obj, Functor.whiskerLeft_app, NatTrans.comp_app,
        Functor.commShiftIso_comp_hom_app, Category.assoc, Functor.map_comp] at h₁ h₂
      rw [← h₂, ← τ.naturality_assoc] at h₁
      rw [← cancel_mono ((c.app Y)⟦a⟧')]
      simpa only [Category.assoc] using (cancel_epi _).1 h₁
    dsimp
    rw [← cancel_mono ((F₂.map f)⟦a⟧'), Category.assoc, ← Functor.map_comp,
      ← τ.naturality, Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc, hY,
      Category.assoc, ← Functor.commShiftIso_hom_naturality, τ.naturality_assoc]

end CategoryTheory.NatTrans.CommShift

namespace DerivedCategory

section Comparison

variable {C₁ C₂ : Type*} [Category.{v} C₁] [Abelian C₁] [IsGrothendieckAbelian.{w} C₁]
  [HasDerivedCategory.{w} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁] [MonoidalPreadditive C₁]
  [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
  [Category.{v} C₂] [Abelian C₂] [IsGrothendieckAbelian.{w} C₂]
  [HasDerivedCategory.{w} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂] [MonoidalPreadditive C₂]
  [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]

local instance hasColimitsOfSize_comparisonShiftKFlat₁ : HasColimitsOfSize.{0, 0} C₁ :=
  hasColimitsOfSizeShrink C₁
local instance hasColimitsOfSize_comparisonShiftKFlat₂ : HasColimitsOfSize.{0, 0} C₂ :=
  hasColimitsOfSizeShrink C₂

variable (F : C₁ ⥤ C₂) [F.Additive] [F.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
  (LF : DerivedCategory C₁ ⥤ DerivedCategory C₂) [LF.CommShift ℤ]
  (cL : Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ Qh) [NatTrans.CommShift cL ℤ]

set_option maxHeartbeats 1000000 in
-- The factorisation through `Qh` elaborates large composites of whiskered transformations.
open Functor in
/-- A natural transformation `τ : LF(Qh X ⊗ᴸ -) ⟶ LF(Qh X) ⊗ᴸ LF(-)` which is compatible, on
the homotopy category, with the comparison `F(X ⊗ -) ⟶ F(X) ⊗ F(-)`, commutes with the shifts,
if `X` and `F(X)` are K-flat and the counit of `LF` is an isomorphism on K-flat complexes. -/
lemma commShift_of_tensorLeft_fac_of_kFlat
    (hcL : ∀ P, (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P → IsIso (cL.app P))
    (hres : ∀ M : DerivedCategory C₁,
      ∃ P, (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P ∧ Nonempty (M ≅ Qh.obj P))
    (X : HomotopyCategory C₁ (.up ℤ))
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
  let G := F.mapHomotopyCategory (.up ℤ)
  let c₂ : Qh ⋙ ((curriedTensor _).obj (Qh.obj X) ⋙ LF) ⟶
      ((curriedTensor _).obj X ⋙ G) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫ whiskerRight (tensorLeftCounit X) LF ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft ((curriedTensor _).obj X) cL ≫
      (Functor.associator _ _ _).inv
  let δ₀ : ((curriedTensor _).obj X ⋙ G) ⋙ Qh ⟶ (G ⋙ (curriedTensor _).obj (G.obj X)) ⋙ Qh :=
    whiskerRight ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app X) Qh
  let c₁ : Qh ⋙ (LF ⋙ (curriedTensor _).obj (LF.obj (Qh.obj X))) ⟶
      (G ⋙ (curriedTensor _).obj (G.obj X)) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerLeft (Qh ⋙ LF) ((curriedTensor _).map (cL.app X)) ≫
      whiskerRight cL ((curriedTensor _).obj (Qh.obj (G.obj X))) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft G (tensorLeftCounit (G.obj X)) ≫
      (Functor.associator _ _ _).inv
  have := isIso_tensorLeftCounit (G.obj X) hFX
  have := hcL X hX
  have fac : whiskerLeft Qh τ ≫ c₁ = c₂ ≫ δ₀ := by
    ext M
    simpa [c₁, c₂, δ₀] using hτ M
  have := commShift_tensorLeftCounit X hX
  have := commShift_tensorLeftCounit (G.obj X) hFX
  have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
  have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
  have := OplaxMonoidal.commShift_mapHomotopyCategoryδNatTrans_app F X
  have : NatTrans.CommShift δ₀ ℤ := by dsimp only [δ₀]; infer_instance
  have : NatTrans.CommShift (whiskerLeft Qh τ ≫ c₁) ℤ := by
    rw [fac]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft_comp τ Qh c₁ (fun M ↦ ?_)
  obtain ⟨P, hP, ⟨e⟩⟩ := hres M
  have := hcL P hP
  refine ⟨P, e.hom, inferInstance, ?_⟩
  simp only [c₁, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  infer_instance

set_option maxHeartbeats 1000000 in
-- The factorisation through `Qh` elaborates large composites of whiskered transformations.
open Functor in
/-- A natural transformation `τ : LF(- ⊗ᴸ Qh X) ⟶ LF(-) ⊗ᴸ LF(Qh X)` which is compatible, on
the homotopy category, with the comparison `F(- ⊗ X) ⟶ F(-) ⊗ F(X)`, commutes with the shifts,
if `X` and `F(X)` are K-flat and the counit of `LF` is an isomorphism on K-flat complexes. -/
lemma commShift_of_tensorRight_fac_of_kFlat
    (hcL : ∀ P, (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P → IsIso (cL.app P))
    (hres : ∀ M : DerivedCategory C₁,
      ∃ P, (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P ∧ Nonempty (M ≅ Qh.obj P))
    (X : HomotopyCategory C₁ (.up ℤ))
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
  let G := F.mapHomotopyCategory (.up ℤ)
  let c₂ : Qh ⋙ ((curriedTensor _).flip.obj (Qh.obj X) ⋙ LF) ⟶
      ((curriedTensor _).flip.obj X ⋙ G) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫ whiskerRight (tensorRightCounit X) LF ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft ((curriedTensor _).flip.obj X) cL ≫
      (Functor.associator _ _ _).inv
  let δ₀ : ((curriedTensor _).flip.obj X ⋙ G) ⋙ Qh ⟶
      (G ⋙ (curriedTensor _).flip.obj (G.obj X)) ⋙ Qh :=
    whiskerRight ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).flipApp X) Qh
  let c₁ : Qh ⋙ (LF ⋙ (curriedTensor _).flip.obj (LF.obj (Qh.obj X))) ⟶
      (G ⋙ (curriedTensor _).flip.obj (G.obj X)) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight cL ((curriedTensor _).flip.obj (LF.obj (Qh.obj X))) ≫
      whiskerLeft (G ⋙ Qh) ((curriedTensor _).flip.map (cL.app X)) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft G (tensorRightCounit (G.obj X)) ≫
      (Functor.associator _ _ _).inv
  have := isIso_tensorRightCounit (G.obj X) hFX
  have := hcL X hX
  have fac : whiskerLeft Qh τ ≫ c₁ = c₂ ≫ δ₀ := by
    ext M
    simpa [c₁, c₂, δ₀] using hτ M
  have := commShift_tensorRightCounit X hX
  have := commShift_tensorRightCounit (G.obj X) hFX
  have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
  have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
  have := OplaxMonoidal.commShift_mapHomotopyCategoryδNatTrans_flipApp F X
  have : NatTrans.CommShift δ₀ ℤ := by dsimp only [δ₀]; infer_instance
  have : NatTrans.CommShift (whiskerLeft Qh τ ≫ c₁) ℤ := by
    rw [fac]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft_comp τ Qh c₁ (fun M ↦ ?_)
  obtain ⟨P, hP, ⟨e⟩⟩ := hres M
  have := hcL P hP
  refine ⟨P, e.hom, inferInstance, ?_⟩
  simp only [c₁, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  infer_instance

end Comparison

end DerivedCategory

namespace CategoryTheory.Functor

universe u u₁ u₂

open _root_.DerivedCategory

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint]
  [F.Monoidal]

/-- The tensor comparison `LF(K ⊗ᴸ -) ⟶ LF K ⊗ᴸ LF(-)` for a fixed `K`. -/
noncomputable abbrev leftDerivedTensorComparisonApp (K : DerivedCategory C) :
    (curriedTensor (DerivedCategory C)).obj K ⋙ F.leftDerivedFunctor ⟶
      F.leftDerivedFunctor ⋙ (curriedTensor (DerivedCategory D)).obj (F.leftDerivedFunctor.obj K) :=
  F.leftDerivedTensorComparison.app K

/-- The tensor comparison `LF(- ⊗ᴸ M) ⟶ LF(-) ⊗ᴸ LF M` for a fixed `M`. -/
noncomputable abbrev leftDerivedTensorComparisonFlipApp (M : DerivedCategory C) :
    (curriedTensor (DerivedCategory C)).flip.obj M ⋙ F.leftDerivedFunctor ⟶
      F.leftDerivedFunctor ⋙
        (curriedTensor (DerivedCategory D)).flip.obj (F.leftDerivedFunctor.obj M) :=
  F.leftDerivedTensorComparison.flipApp M

variable [F.leftDerivedFunctor.CommShift ℤ] [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ]

lemma commShift_leftDerivedTensorComparisonApp_Qh_obj (X : HomotopyCategory C (.up ℤ))
    (hX : F.kFlatKFlatMap X) :
    NatTrans.CommShift (F.leftDerivedTensorComparisonApp (Qh.obj X)) ℤ :=
  DerivedCategory.commShift_of_tensorLeft_fac_of_kFlat F F.leftDerivedFunctor
    F.leftDerivedFunctorCounit (fun P hP ↦ F.isIso_leftDerivedFunctorCounit_app_of_kFlat' P hP)
    (fun M ↦ ⟨_, (F.exists_kFlatKFlatMap_iso M).choose_spec.1.1,
      ⟨(F.exists_kFlatKFlatMap_iso M).choose_spec.2.some.symm⟩⟩) X hX.1 hX.2 _ (fun M ↦ by
      have := F.leftDerivedTensorComparison_app_app_comp_counit X M
      simp only [derivedTensorLeftDerivedCounit, leftDerivedDerivedTensorCounit,
        NatTrans.comp_app, Functor.comp_obj, Functor.whiskeringLeft₂_map_app_app_app_app,
        Functor.whiskeringLeft₂_obj_map_app_app_app, Functor.whiskeringLeft₂_obj_obj_map_app_app,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.postcompose₂_obj_obj_obj_obj,
        Functor.LaxMonoidal.μNatTrans_app_app, Functor.postcompose₂_obj_map_app_app,
        Functor.postcompose₂_map_app_app_app, curriedTensor_obj_obj, Category.assoc] at this ⊢
      exact this)

lemma commShift_leftDerivedTensorComparisonFlipApp_Qh_obj (X : HomotopyCategory C (.up ℤ))
    (hX : F.kFlatKFlatMap X) :
    NatTrans.CommShift (F.leftDerivedTensorComparisonFlipApp (Qh.obj X)) ℤ :=
  DerivedCategory.commShift_of_tensorRight_fac_of_kFlat F F.leftDerivedFunctor
    F.leftDerivedFunctorCounit (fun P hP ↦ F.isIso_leftDerivedFunctorCounit_app_of_kFlat' P hP)
    (fun M ↦ ⟨_, (F.exists_kFlatKFlatMap_iso M).choose_spec.1.1,
      ⟨(F.exists_kFlatKFlatMap_iso M).choose_spec.2.some.symm⟩⟩) X hX.1 hX.2 _ (fun M ↦ by
      have := F.leftDerivedTensorComparison_app_app_comp_counit M X
      simp only [derivedTensorLeftDerivedCounit, leftDerivedDerivedTensorCounit,
        NatTrans.comp_app, Functor.comp_obj, Functor.whiskeringLeft₂_map_app_app_app_app,
        Functor.whiskeringLeft₂_obj_map_app_app_app, Functor.whiskeringLeft₂_obj_obj_map_app_app,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.postcompose₂_obj_obj_obj_obj,
        Functor.LaxMonoidal.μNatTrans_app_app, Functor.postcompose₂_obj_map_app_app,
        Functor.postcompose₂_map_app_app_app, curriedTensor_obj_obj, Category.assoc,
        Functor.flip_obj_obj, flipFunctor_map_app_app] at this ⊢
      exact this)

omit [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ] in
lemma commShift_leftDerivedTensorComparisonApp_of_iso {K K' : DerivedCategory C} (e : K ≅ K')
    [NatTrans.CommShift (F.leftDerivedTensorComparisonApp K') ℤ] :
    NatTrans.CommShift (F.leftDerivedTensorComparisonApp K) ℤ := by
  have eq : F.leftDerivedTensorComparisonApp K =
      Functor.whiskerRight ((curriedTensor _).map e.hom) F.leftDerivedFunctor ≫
        F.leftDerivedTensorComparisonApp K' ≫
        Functor.whiskerLeft F.leftDerivedFunctor
          ((curriedTensor _).map (F.leftDerivedFunctor.map e.inv)) := by
    have := F.leftDerivedTensorComparison.naturality e.hom
    ext M
    have := congr_app this M
    dsimp at this ⊢
    rw [reassoc_of% this]
    simp [← MonoidalCategory.comp_whiskerRight, ← Functor.map_comp]
  rw [eq]
  infer_instance

omit [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ] in
lemma commShift_leftDerivedTensorComparisonFlipApp_of_iso {M M' : DerivedCategory C}
    (e : M ≅ M') [NatTrans.CommShift (F.leftDerivedTensorComparisonFlipApp M') ℤ] :
    NatTrans.CommShift (F.leftDerivedTensorComparisonFlipApp M) ℤ := by
  have eq : F.leftDerivedTensorComparisonFlipApp M =
      Functor.whiskerRight ((curriedTensor _).flip.map e.hom) F.leftDerivedFunctor ≫
        F.leftDerivedTensorComparisonFlipApp M' ≫
        Functor.whiskerLeft F.leftDerivedFunctor
          ((curriedTensor _).flip.map (F.leftDerivedFunctor.map e.inv)) := by
    ext K
    have := (F.leftDerivedTensorComparison.app K).naturality e.hom
    dsimp at this ⊢
    rw [reassoc_of% this]
    simp [← MonoidalCategory.whiskerLeft_comp, ← Functor.map_comp]
  rw [eq]
  infer_instance

/-- **The tensor comparison of a left derived functor commutes with the shifts of the second
factor**, for any shift structure on `LF` for which the counit commutes with the shifts. -/
instance commShift_leftDerivedTensorComparisonApp (K : DerivedCategory C) :
    NatTrans.CommShift (F.leftDerivedTensorComparisonApp K) ℤ := by
  obtain ⟨P, hP, ⟨e⟩⟩ := F.exists_kFlatKFlatMap_iso K
  have := F.commShift_leftDerivedTensorComparisonApp_Qh_obj P hP
  exact F.commShift_leftDerivedTensorComparisonApp_of_iso e.symm

/-- **The tensor comparison of a left derived functor commutes with the shifts of the first
factor**, for any shift structure on `LF` for which the counit commutes with the shifts. -/
instance commShift_leftDerivedTensorComparisonFlipApp (M : DerivedCategory C) :
    NatTrans.CommShift (F.leftDerivedTensorComparisonFlipApp M) ℤ := by
  obtain ⟨P, hP, ⟨e⟩⟩ := F.exists_kFlatKFlatMap_iso M
  have := F.commShift_leftDerivedTensorComparisonFlipApp_Qh_obj P hP
  exact F.commShift_leftDerivedTensorComparisonFlipApp_of_iso e.symm

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

section Transpose

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.CommShift A] [G.CommShift A] [adj.CommShift A] {U : E ⥤ C} {V : E ⥤ D} [U.CommShift A]
  [V.CommShift A]

/-- A natural transformation `α : U ⋙ F ⟶ V` commutes with the shifts if its transpose
`β : U ⟶ V ⋙ G` under an adjunction `F ⊣ G` compatible with the shifts does. -/
lemma commShift_of_commShift_transpose (α : U ⋙ F ⟶ V) (β : U ⟶ V ⋙ G)
    [NatTrans.CommShift β A] (h : ∀ X, β.app X = adj.unit.app (U.obj X) ≫ G.map (α.app X)) :
    NatTrans.CommShift α A := by
  have eq : α = Functor.whiskerRight β F ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft V adj.counit ≫ V.rightUnitor.hom := by
    ext X
    simp [h]
  rw [eq]
  infer_instance

end Transpose

section Derived

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The unit of the derived adjunction `Lf ⊣ D(g)` of an adjunction `f ⊣ g` with `g` exact, on
the image `Qh X` of a complex, is the levelwise unit read through the counit of `Lf`. -/
@[reassoc]
lemma derivedAdjunction_ofNatIsoRight_unit_app_Qh_comp (adj : f ⊣ g)
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (adj.derivedAdjunction.ofNatIsoRight g.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Qh.obj X) ≫
      g.mapDerivedCategory.map (f.leftDerivedFunctorCounit.app X) =
    DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X) ≫
      g.mapDerivedCategoryFactorsh.inv.app ((f.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) := by
  have h₁ := adj.derivedAdjunction_unit_app_Qh_fac X
  have h₂ := NatTrans.congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((f.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)
  have h₃ := g.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (f.leftDerivedFunctorCounit.app X)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  erw [← h₃, reassoc_of% h₁]
  rw [← h₂]
  rfl

/-- The counit `Qh ⋙ Lf ⟶ K(f) ⋙ Qh` of the left derived functor of `f` commutes with the
shifts, for the shift structure of `Lf` induced, as a left adjoint, by the one of `D(g)`. -/
lemma commShift_leftDerivedFunctorCounit_of_adjunction (adj : f ⊣ g) :
    letI := (adj.derivedAdjunction.ofNatIsoRight
      g.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
    NatTrans.CommShift f.leftDerivedFunctorCounit ℤ := by
  let adj' := adj.derivedAdjunction.ofNatIsoRight g.rightDerivedFunctorIsoMapDerivedCategory
  let := adj'.leftAdjointCommShift ℤ
  have := adj'.commShift_of_rightAdjoint ℤ
  refine adj'.commShift_of_commShift_transpose f.leftDerivedFunctorCounit
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (f.mapHomotopyCategory (ComplexShape.up ℤ))
        g.mapDerivedCategoryFactorsh.inv ≫ (Functor.associator _ _ _).inv) (fun X ↦ ?_)
  rw [adj.derivedAdjunction_ofNatIsoRight_unit_app_Qh_comp X]
  simp

end Derived

end CategoryTheory.Adjunction
