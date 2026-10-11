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

lemma isIso_eTruncLTι_app_map_eTruncLT_obj_obj (i : EInt) (X : C) :
    IsIso ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))) := by
  induction i using WithBotTop.rec with
  | bot =>
    refine ⟨0, (Functor.zero_obj _).eq_of_src _ _, ?_⟩
    exact (F.map_isZero (Functor.zero_obj X)).eq_of_src _ _
  | coe n =>
    have := IsTExact.isLE_obj t₁ t₂ F ((t₁.truncLT n).obj X) (n - 1)
    exact (t₂.isLE_iff_isIso_truncLTι_app (n - 1) n (by lia) _).1 this
  | top => dsimp; infer_instance

lemma isIso_eTruncLT_obj_map_map_eTruncLTι_app (i : EInt) (X : C) :
    IsIso ((t₂.eTruncLT.obj i).map (F.map ((t₁.eTruncLTι i).app X))) := by
  induction i using WithBotTop.rec with
  | bot =>
    exact ⟨0, (Functor.zero_obj _).eq_of_src _ _, (Functor.zero_obj _).eq_of_src _ _⟩
  | coe n =>
    have := IsTExact.isGE_obj t₁ t₂ F ((t₁.truncGE n).obj X) n
    exact t₂.isIso₁_truncLT_map_of_isGE (F.mapTriangle.obj ((t₁.triangleLTGE n).obj X))
      (F.map_distinguished _ (t₁.triangleLTGE_distinguished n X)) n this
  | top => dsimp; infer_instance

lemma isIso_eTruncGEπ_app_map_eTruncGE_obj_obj (i : EInt) (X : C) :
    IsIso ((t₂.eTruncGEπ i).app (F.obj ((t₁.eTruncGE.obj i).obj X))) := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe n =>
    have := IsTExact.isGE_obj t₁ t₂ F ((t₁.truncGE n).obj X) n
    exact (t₂.isGE_iff_isIso_truncGEπ_app n _).1 this
  | top =>
    refine ⟨0, ?_, (Functor.zero_obj _).eq_of_src _ _⟩
    exact (F.map_isZero (Functor.zero_obj X)).eq_of_src _ _

lemma isIso_eTruncGE_obj_map_map_eTruncGEπ_app (i : EInt) (X : C) :
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

/-- The component at `X` of `Functor.eTruncLTIso`. -/
noncomputable def eTruncLTIsoApp (i : EInt) (X : C) :
    F.obj ((t₁.eTruncLT.obj i).obj X) ≅ (t₂.eTruncLT.obj i).obj (F.obj X) :=
  have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  have := F.isIso_eTruncLT_obj_map_map_eTruncLTι_app (t₁ := t₁) (t₂ := t₂) i X
  (asIso ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)))).symm ≪≫
    asIso ((t₂.eTruncLT.obj i).map (F.map ((t₁.eTruncLTι i).app X)))

@[reassoc]
lemma eTruncLTι_app_eTruncLTIsoApp_hom (i : EInt) (X : C) :
    (t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)) ≫
      (F.eTruncLTIsoApp t₁ t₂ i X).hom =
      (t₂.eTruncLT.obj i).map (F.map ((t₁.eTruncLTι i).app X)) := by
  have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  simp [eTruncLTIsoApp]

@[reassoc (attr := simp)]
lemma eTruncLTIsoApp_hom_eTruncLTι_app (i : EInt) (X : C) :
    (F.eTruncLTIsoApp t₁ t₂ i X).hom ≫ (t₂.eTruncLTι i).app (F.obj X) =
      F.map ((t₁.eTruncLTι i).app X) := by
  have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  rw [← cancel_epi ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))),
    reassoc_of% (F.eTruncLTι_app_eTruncLTIsoApp_hom t₁ t₂ i X)]
  exact (t₂.eTruncLTι i).naturality _

/-- The component at `X` of `Functor.eTruncGEIso`. -/
noncomputable def eTruncGEIsoApp (i : EInt) (X : C) :
    F.obj ((t₁.eTruncGE.obj i).obj X) ≅ (t₂.eTruncGE.obj i).obj (F.obj X) :=
  have := F.isIso_eTruncGEπ_app_map_eTruncGE_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) i X
  asIso ((t₂.eTruncGEπ i).app (F.obj ((t₁.eTruncGE.obj i).obj X))) ≪≫
    (asIso ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X)))).symm

@[reassoc]
lemma eTruncGEIsoApp_hom_eTruncGE_map (i : EInt) (X : C) :
    (F.eTruncGEIsoApp t₁ t₂ i X).hom ≫ (t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X)) =
      (t₂.eTruncGEπ i).app (F.obj ((t₁.eTruncGE.obj i).obj X)) := by
  have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) i X
  simp [eTruncGEIsoApp]

@[reassoc (attr := simp)]
lemma eTruncGEπ_app_eTruncGEIsoApp_hom (i : EInt) (X : C) :
    F.map ((t₁.eTruncGEπ i).app X) ≫ (F.eTruncGEIsoApp t₁ t₂ i X).hom =
      (t₂.eTruncGEπ i).app (F.obj X) := by
  have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) i X
  rw [← cancel_mono ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X))), Category.assoc,
    F.eTruncGEIsoApp_hom_eTruncGE_map t₁ t₂ i X]
  exact (t₂.eTruncGEπ i).naturality _

/-- A t-exact functor commutes with the truncation functors `t.eTruncLT.obj i`. -/
noncomputable def eTruncLTIso (i : EInt) :
    t₁.eTruncLT.obj i ⋙ F ≅ F ⋙ t₂.eTruncLT.obj i :=
  NatIso.ofComponents (F.eTruncLTIsoApp t₁ t₂ i) (fun {X Y} f ↦ by
    have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
    rw [← cancel_epi ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))),
      F.eTruncLTι_app_eTruncLTIsoApp_hom_assoc t₁ t₂]
    have h := (t₂.eTruncLTι i).naturality (F.map ((t₁.eTruncLT.obj i).map f))
    dsimp at h ⊢
    rw [← reassoc_of% h, F.eTruncLTι_app_eTruncLTIsoApp_hom t₁ t₂, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    exact (t₁.eTruncLTι i).naturality f)

@[simp]
lemma eTruncLTIso_hom_app (i : EInt) (X : C) :
    (F.eTruncLTIso t₁ t₂ i).hom.app X = (F.eTruncLTIsoApp t₁ t₂ i X).hom := rfl

/-- A t-exact functor commutes with the truncation functors `t.eTruncGE.obj i`. -/
noncomputable def eTruncGEIso (i : EInt) :
    t₁.eTruncGE.obj i ⋙ F ≅ F ⋙ t₂.eTruncGE.obj i :=
  NatIso.ofComponents (F.eTruncGEIsoApp t₁ t₂ i) (fun {X Y} f ↦ by
    have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) i Y
    rw [← cancel_mono ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app Y))),
      Category.assoc, F.eTruncGEIsoApp_hom_eTruncGE_map t₁ t₂]
    have h := (t₂.eTruncGEπ i).naturality (F.map ((t₁.eTruncGE.obj i).map f))
    dsimp at h ⊢
    rw [h, Category.assoc, ← Functor.map_comp, ← F.map_comp, ← t₁.eTruncGEπ_naturality,
      F.map_comp, Functor.map_comp, F.eTruncGEIsoApp_hom_eTruncGE_map_assoc t₁ t₂])

@[simp]
lemma eTruncGEIso_hom_app (i : EInt) (X : C) :
    (F.eTruncGEIso t₁ t₂ i).hom.app X = (F.eTruncGEIsoApp t₁ t₂ i X).hom := rfl

@[reassoc]
lemma eTruncLT_map_app_eTruncLTIso_hom_app {i j : EInt} (f : i ⟶ j) (X : C) :
    F.map ((t₁.eTruncLT.map f).app X) ≫ (F.eTruncLTIso t₁ t₂ j).hom.app X =
      (F.eTruncLTIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncLT.map f).app (F.obj X) := by
  have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  simp only [eTruncLTIso_hom_app]
  rw [← cancel_epi ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))),
    F.eTruncLTι_app_eTruncLTIsoApp_hom_assoc t₁ t₂]
  have h : (t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)) ≫
      F.map ((t₁.eTruncLT.map f).app X) =
      (t₂.eTruncLT.map f).app (F.obj ((t₁.eTruncLT.obj i).obj X)) ≫
        (t₂.eTruncLT.obj j).map (F.map ((t₁.eTruncLT.map f).app X)) ≫
        (t₂.eTruncLTι j).app (F.obj ((t₁.eTruncLT.obj j).obj X)) := by
    have h₁ := (t₂.eTruncLTι j).naturality (F.map ((t₁.eTruncLT.map f).app X))
    dsimp at h₁
    rw [h₁, t₂.eTruncLT_map_app_eTruncLTι_app_assoc]
  rw [reassoc_of% h, F.eTruncLTι_app_eTruncLTIsoApp_hom t₁ t₂, ← Functor.map_comp, ← F.map_comp,
    t₁.eTruncLT_map_app_eTruncLTι_app]
  exact ((t₂.eTruncLT.map f).naturality _).symm

@[reassoc]
lemma eTruncGE_map_app_eTruncGEIso_hom_app {i j : EInt} (f : i ⟶ j) (X : C) :
    F.map ((t₁.eTruncGE.map f).app X) ≫ (F.eTruncGEIso t₁ t₂ j).hom.app X =
      (F.eTruncGEIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncGE.map f).app (F.obj X) := by
  have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) j X
  simp only [eTruncGEIso_hom_app]
  rw [← cancel_mono ((t₂.eTruncGE.obj j).map (F.map ((t₁.eTruncGEπ j).app X))), Category.assoc,
    Category.assoc, F.eTruncGEIsoApp_hom_eTruncGE_map t₁ t₂]
  have h : (t₂.eTruncGE.map f).app (F.obj X) ≫
      (t₂.eTruncGE.obj j).map (F.map ((t₁.eTruncGEπ j).app X)) =
      (t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X)) ≫
        (t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGE.map f).app X)) ≫
        (t₂.eTruncGE.map f).app (F.obj ((t₁.eTruncGE.obj j).obj X)) := by
    rw [← Functor.map_comp_assoc, ← F.map_comp, t₁.eTruncGEπ_app_eTruncGE_map_app]
    exact ((t₂.eTruncGE.map f).naturality _).symm
  rw [h, reassoc_of% (F.eTruncGEIsoApp_hom_eTruncGE_map t₁ t₂ i X)]
  have h₂ := (t₂.eTruncGEπ i).naturality (F.map ((t₁.eTruncGE.map f).app X))
  dsimp at h₂
  rw [← reassoc_of% h₂, t₂.eTruncGEπ_app_eTruncGE_map_app]

/-- A t-exact triangulated functor commutes with the connecting homomorphisms of the truncation
triangles. -/
@[reassoc]
lemma eTruncGEδLT_comm (i : EInt) (X : C) :
    F.map ((t₁.eTruncGEδLT.app i).app X) ≫ (F.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((F.eTruncLTIso t₁ t₂ i).hom.app X)⟦(1 : ℤ)⟧' =
      (F.eTruncGEIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncGEδLT.app i).app (F.obj X) := by
  induction i using WithBotTop.rec with
  | bot => simp [TStructure.eTruncGEδLT]
  | top => simp [TStructure.eTruncGEδLT]
  | coe n =>
    let T₁ := F.mapTriangle.obj ((t₁.triangleLTGE n).obj X)
    have hT₁ : T₁ ∈ distTriang D := F.map_distinguished _ (t₁.triangleLTGE_distinguished n X)
    have hT₂ := t₂.triangleLTGE_distinguished n (F.obj X)
    have h₁ : t₂.IsLE T₁.obj₁ (n - 1) := IsTExact.isLE_obj t₁ t₂ F _ _
    have h₃ : t₂.IsGE T₁.obj₃ n := IsTExact.isGE_obj t₁ t₂ F _ _
    have : t₂.IsLE (T₁.obj₁⟦(1 : ℤ)⟧) (n - 2) := t₂.isLE_shift _ (n - 1) 1 (n - 2) (by lia)
    obtain ⟨φ, hφ⟩ := t₂.triangle_map_exists hT₁ hT₂ (𝟙 _) (n - 1) n h₁ inferInstance
    have e₁ : φ.hom₁ = (F.eTruncLTIsoApp t₁ t₂ n X).hom := by
      apply t₂.to_truncLT_obj_ext
      have := φ.comm₁
      rw [hφ, Category.comp_id] at this
      exact this.symm.trans (F.eTruncLTIsoApp_hom_eTruncLTι_app t₁ t₂ n X).symm
    let ψ : T₁.obj₃ ⟶ ((t₂.triangleLTGE n).obj (F.obj X)).obj₃ :=
      (F.eTruncGEIsoApp t₁ t₂ n X).hom
    have e₃ : φ.hom₃ = ψ := by
      rw [← sub_eq_zero]
      obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ T₁ hT₁ (φ.hom₃ - ψ) (by
        have := φ.comm₂
        rw [hφ, Category.id_comp] at this
        rw [Preadditive.comp_sub, this, sub_eq_zero]
        exact (F.eTruncGEπ_app_eTruncGEIsoApp_hom t₁ t₂ n X).symm)
      rw [hg, t₂.zero_of_isLE_of_isGE g (n - 2) n (by lia) inferInstance inferInstance,
        comp_zero]
    have := φ.comm₃
    rw [e₁, e₃] at this
    exact (Category.assoc _ _ _).symm.trans this

end Functor

end CategoryTheory
