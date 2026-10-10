/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-!
# t-exact functors and the spectral objects attached to t-structures

Let `F : C ⥤ D` be a triangulated functor between triangulated categories equipped with
t-structures `t₁` and `t₂`. We say that `F` is *t-exact* (`Functor.IsTExact`) if it preserves
the objects which are `≤ n` and the objects which are `≥ n` for all `n : ℤ`. A t-exact functor
commutes with the truncation functors (`Functor.eTruncLTIso`, `Functor.eTruncGEIso`), compatibly
with the connecting homomorphisms of the truncation triangles
(`Functor.eTruncGEδLT_comm`). As a consequence, the image under `F` of the spectral object
`t₁.spectralObject X` consisting of all the truncations of `X` identifies to the spectral object
`t₂.spectralObject (F.obj X)` (`Functor.mapTriangulatedSpectralObjectIso`), naturally in `X`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated ComposableArrows Triangulated

variable {C D : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [CategoryTheory.IsTriangulated C] [CategoryTheory.IsTriangulated D]
  (t₁ : TStructure C) (t₂ : TStructure D)

namespace Functor

/-- A functor `F : C ⥤ D` between categories equipped with t-structures `t₁` and `t₂` is
*t-exact* if it sends objects which are `≤ n` (resp. `≥ n`) for `t₁` to objects which are
`≤ n` (resp. `≥ n`) for `t₂`. -/
class IsTExact (F : C ⥤ D) : Prop where
  isLE (X : C) (n : ℤ) [t₁.IsLE X n] : t₂.IsLE (F.obj X) n
  isGE (X : C) (n : ℤ) [t₁.IsGE X n] : t₂.IsGE (F.obj X) n

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t₁ t₂]

namespace IsTExact

include t₂ in
lemma isLE_obj (X : C) (n : ℤ) [t₁.IsLE X n] : t₂.IsLE (F.obj X) n :=
  IsTExact.isLE (t₁ := t₁) (t₂ := t₂) (F := F) X n

include t₁ in
lemma isGE_obj (X : C) (n : ℤ) [t₁.IsGE X n] : t₂.IsGE (F.obj X) n :=
  IsTExact.isGE (t₁ := t₁) (t₂ := t₂) (F := F) X n

end IsTExact

section

variable {t₁ t₂}

instance isIso_eTruncLTι_app_map_eTruncLT_obj_obj (i : EInt) (X : C) :
    IsIso ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))) := by
  induction i using WithBotTop.rec with
  | bot =>
    refine ⟨0, (Functor.zero_obj _).eq_of_src _ _, ?_⟩
    exact (F.map_isZero (Functor.zero_obj X)).eq_of_src _ _
  | coe n =>
    have := IsTExact.isLE_obj t₁ t₂ F ((t₁.truncLT n).obj X) (n - 1)
    exact (t₂.isLE_iff_isIso_truncLTι_app (n - 1) n (by lia) _).1 this
  | top => dsimp; infer_instance

instance isIso_eTruncLT_obj_map_map_eTruncLTι_app (i : EInt) (X : C) :
    IsIso ((t₂.eTruncLT.obj i).map (F.map ((t₁.eTruncLTι i).app X))) := by
  induction i using WithBotTop.rec with
  | bot =>
    exact ⟨0, (Functor.zero_obj _).eq_of_src _ _, (Functor.zero_obj _).eq_of_src _ _⟩
  | coe n =>
    have := IsTExact.isGE_obj t₁ t₂ F ((t₁.truncGE n).obj X) n
    exact t₂.isIso₁_truncLT_map_of_isGE (F.mapTriangle.obj ((t₁.triangleLTGE n).obj X))
      (F.map_distinguished _ (t₁.triangleLTGE_distinguished n X)) n this
  | top => dsimp; infer_instance

instance isIso_eTruncGEπ_app_map_eTruncGE_obj_obj (i : EInt) (X : C) :
    IsIso ((t₂.eTruncGEπ i).app (F.obj ((t₁.eTruncGE.obj i).obj X))) := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe n =>
    have := IsTExact.isGE_obj t₁ t₂ F ((t₁.truncGE n).obj X) n
    exact (t₂.isGE_iff_isIso_truncGEπ_app n _).1 this
  | top =>
    refine ⟨0, ?_, (Functor.zero_obj _).eq_of_src _ _⟩
    exact (F.map_isZero (Functor.zero_obj X)).eq_of_src _ _

instance isIso_eTruncGE_obj_map_map_eTruncGEπ_app (i : EInt) (X : C) :
    IsIso ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X))) := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe n =>
    have := IsTExact.isLE_obj t₁ t₂ F ((t₁.truncLT n).obj X) (n - 1)
    exact t₂.isIso₂_truncGE_map_of_isLE (F.mapTriangle.obj ((t₁.triangleLTGE n).obj X))
      (F.map_distinguished _ (t₁.triangleLTGE_distinguished n X)) (n - 1) n (by lia) this
  | top =>
    exact ⟨0, (Functor.zero_obj _).eq_of_src _ _, (Functor.zero_obj _).eq_of_src _ _⟩

end

/-- A t-exact functor commutes with the truncation functors `t.eTruncLT.obj i`. -/
noncomputable def eTruncLTIso (i : EInt) :
    t₁.eTruncLT.obj i ⋙ F ≅ F ⋙ t₂.eTruncLT.obj i :=
  NatIso.ofComponents (fun X ↦
    (asIso ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)))).symm ≪≫
      asIso ((t₂.eTruncLT.obj i).map (F.map ((t₁.eTruncLTι i).app X)))) (fun {X Y} f ↦ by
    rw [← cancel_epi ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)))]
    simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
      IsIso.hom_inv_id_assoc]
    rw [← t₂.eTruncLTι_naturality_assoc, IsIso.hom_inv_id_assoc, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, t₁.eTruncLTι_naturality])

@[reassoc (attr := simp)]
lemma eTruncLTIso_hom_app_eTruncLTι_app (i : EInt) (X : C) :
    (F.eTruncLTIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncLTι i).app (F.obj X) =
      F.map ((t₁.eTruncLTι i).app X) := by
  simp [eTruncLTIso, t₂.eTruncLTι_naturality]

/-- A t-exact functor commutes with the truncation functors `t.eTruncGE.obj i`. -/
noncomputable def eTruncGEIso (i : EInt) :
    t₁.eTruncGE.obj i ⋙ F ≅ F ⋙ t₂.eTruncGE.obj i :=
  NatIso.ofComponents (fun X ↦
    asIso ((t₂.eTruncGEπ i).app (F.obj ((t₁.eTruncGE.obj i).obj X))) ≪≫
      (asIso ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X)))).symm)
    (fun {X Y} f ↦ by
    rw [← cancel_mono ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app Y)))]
    simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← Functor.map_comp, ← Functor.map_comp, ← t₁.eTruncGEπ_naturality, Functor.map_comp,
      Functor.map_comp, IsIso.inv_hom_id_assoc, t₂.eTruncGEπ_naturality])

@[reassoc (attr := simp)]
lemma eTruncGEπ_app_eTruncGEIso_hom_app (i : EInt) (X : C) :
    F.map ((t₁.eTruncGEπ i).app X) ≫ (F.eTruncGEIso t₁ t₂ i).hom.app X =
      (t₂.eTruncGEπ i).app (F.obj X) := by
  simp [eTruncGEIso, ← t₂.eTruncGEπ_naturality_assoc]

@[reassoc]
lemma eTruncLT_map_app_eTruncLTIso_hom_app {i j : EInt} (f : i ⟶ j) (X : C) :
    F.map ((t₁.eTruncLT.map f).app X) ≫ (F.eTruncLTIso t₁ t₂ j).hom.app X =
      (F.eTruncLTIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncLT.map f).app (F.obj X) := by
  rw [← cancel_epi ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)))]
  simp only [eTruncLTIso, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    asIso_hom, IsIso.hom_inv_id_assoc]
  have h : (t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)) ≫
      F.map ((t₁.eTruncLT.map f).app X) =
      (t₂.eTruncLT.map f).app (F.obj ((t₁.eTruncLT.obj i).obj X)) ≫
        (t₂.eTruncLT.obj j).map (F.map ((t₁.eTruncLT.map f).app X)) ≫
        (t₂.eTruncLTι j).app (F.obj ((t₁.eTruncLT.obj j).obj X)) := by
    rw [t₂.eTruncLTι_naturality, t₂.eTruncLT_map_app_eTruncLTι_app_assoc]
  rw [reassoc_of% h, IsIso.hom_inv_id_assoc, ← Functor.map_comp, ← F.map_comp,
    t₁.eTruncLT_map_app_eTruncLTι_app]
  exact ((t₂.eTruncLT.map f).naturality _).symm

@[reassoc]
lemma eTruncGE_map_app_eTruncGEIso_hom_app {i j : EInt} (f : i ⟶ j) (X : C) :
    F.map ((t₁.eTruncGE.map f).app X) ≫ (F.eTruncGEIso t₁ t₂ j).hom.app X =
      (F.eTruncGEIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncGE.map f).app (F.obj X) := by
  rw [← cancel_mono ((t₂.eTruncGE.obj j).map (F.map ((t₁.eTruncGEπ j).app X)))]
  simp only [eTruncGEIso, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    asIso_hom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have h : (t₂.eTruncGE.map f).app (F.obj X) ≫
      (t₂.eTruncGE.obj j).map (F.map ((t₁.eTruncGEπ j).app X)) =
      (t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X)) ≫
        (t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGE.map f).app X)) ≫
        (t₂.eTruncGE.map f).app (F.obj ((t₁.eTruncGE.obj j).obj X)) := by
    rw [← Functor.map_comp_assoc, ← F.map_comp, t₁.eTruncGEπ_app_eTruncGE_map_app]
    exact (t₂.eTruncGE.map f).naturality _
  rw [h, IsIso.inv_hom_id_assoc, t₂.eTruncGEπ_naturality_assoc,
    t₂.eTruncGEπ_app_eTruncGE_map_app]

/-- A t-exact triangulated functor commutes with the connecting homomorphisms of the truncation
triangles. -/
@[reassoc]
lemma eTruncGEδLT_comm (i : EInt) (X : C) :
    F.map ((t₁.eTruncGEδLT.app i).app X) ≫ (F.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((F.eTruncLTIso t₁ t₂ i).hom.app X)⟦(1 : ℤ)⟧' =
      (F.eTruncGEIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncGEδLT.app i).app (F.obj X) := by
  sorry

end Functor

end CategoryTheory
