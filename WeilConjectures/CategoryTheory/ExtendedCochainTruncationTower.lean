/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedUpperTruncationComparison
public import Mathlib.Order.WithBotTop

/-! Upper smart truncation towers, with their zero and full-complex endpoints.
Source: Stacks Project, Tags 0118, 0156 and 015X.
(blueprint: def-sp-extended-smart-truncation-tower).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

instance extendedTruncationInclusion_mono (K : CochainComplex C ℤ) (q : ℤ) :
    Mono (K.ιTruncLE q) :=
  inferInstanceAs (Mono (HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE q)))

/-- The upper smart truncation strictly below an extended integer. -/
noncomputable def extendedTruncationTower (K : CochainComplex C ℤ) :
    EInt ⥤ CochainComplex C ℤ where
  obj := WithBotTop.rec 0 (fun q ↦ K.truncLE (q - 1)) K
  map {a b} f := by
    induction a using WithBotTop.rec with
    | bot => exact 0
    | coe a =>
      induction b using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact DerivedCategory.truncLECutoffMap K (by
          have := leOfHom f
          simp only [WithBotTop.coe_le_coe] at this
          omega)
      | top => exact K.ιTruncLE (a - 1)
    | top =>
      induction b using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 K
  map_id a := by
    induction a using WithBotTop.rec with
    | bot => exact (isZero_zero _).eq_of_src _ _
    | coe a =>
      change DerivedCategory.truncLECutoffMap K (show a - 1 ≤ a - 1 by rfl) = 𝟙 _
      apply (cancel_mono (K.ιTruncLE (a - 1))).1
      rw [DerivedCategory.truncLECutoffMap_ι, Category.id_comp]
    | top => rfl
  map_comp {a b c} f g := by
    have hf := leOfHom f
    have hg := leOfHom g
    induction a using WithBotTop.rec <;> induction b using WithBotTop.rec <;>
      induction c using WithBotTop.rec
    all_goals first
    | exact (isZero_zero _).eq_of_src _ _
    | (solve | simp_all only [le_bot_iff, top_le_iff, WithBotTop.coe_ne_bot,
        WithBotTop.coe_ne_top, top_ne_bot])
    | simp_all only [WithBotTop.rec_coe, WithBotTop.rec_top, Category.comp_id]
    case coe.coe.coe a b c =>
      change DerivedCategory.truncLECutoffMap K _ =
        DerivedCategory.truncLECutoffMap K _ ≫ DerivedCategory.truncLECutoffMap K _
      apply (cancel_mono (K.ιTruncLE (c - 1))).1
      rw [DerivedCategory.truncLECutoffMap_ι, Category.assoc,
        DerivedCategory.truncLECutoffMap_ι, DerivedCategory.truncLECutoffMap_ι]
    case coe.coe.top a b =>
      change K.ιTruncLE (a - 1) = DerivedCategory.truncLECutoffMap K _ ≫ K.ιTruncLE (b - 1)
      exact (DerivedCategory.truncLECutoffMap_ι K _).symm

/-- Inclusions into the original complex normalize every tower arrow. -/
noncomputable def extendedTruncationTowerι (K : CochainComplex C ℤ) :
    extendedTruncationTower K ⟶ (Functor.const EInt).obj K where
  app := WithBotTop.rec 0 (fun q ↦ K.ιTruncLE (q - 1)) (𝟙 K)
  naturality a b f := by
    have hf := leOfHom f
    induction a using WithBotTop.rec <;> induction b using WithBotTop.rec
    all_goals first
    | exact (isZero_zero _).eq_of_src _ _
    | simp_all [extendedTruncationTower]
    case coe.coe a b =>
      change DerivedCategory.truncLECutoffMap K _ ≫ K.ιTruncLE (b - 1) = _
      simpa only [Functor.const_obj_map, Category.comp_id] using
        DerivedCategory.truncLECutoffMap_ι K
          (show a - 1 ≤ b - 1 by
            have := leOfHom f
            simp only [WithBotTop.coe_le_coe] at this
            omega)

/-- Complex maps restrict to all extended cutoffs. -/
noncomputable def extendedTruncationTowerMap {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    extendedTruncationTower K ⟶ extendedTruncationTower L where
  app := WithBotTop.rec 0 (fun q ↦ truncLEMap f (q - 1)) f
  naturality a b g := by
    have hg := leOfHom g
    induction a using WithBotTop.rec <;> induction b using WithBotTop.rec
    all_goals first
    | exact (isZero_zero _).eq_of_src _ _
    | simp_all only [le_bot_iff, top_le_iff, WithBotTop.coe_ne_bot,
        WithBotTop.coe_ne_top, top_ne_bot, extendedTruncationTower, WithBotTop.rec_coe,
        WithBotTop.rec_top, Category.comp_id, Category.id_comp,
        ιTruncLE_naturality]
    case coe.coe a b =>
      change DerivedCategory.truncLECutoffMap K _ ≫ truncLEMap f (b - 1) =
        truncLEMap f (a - 1) ≫ DerivedCategory.truncLECutoffMap L _
      exact DerivedCategory.truncLECutoffMap_naturality f _

@[reassoc]
theorem extendedTruncationTowerMap_app_ι {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (a : EInt) :
    (extendedTruncationTowerMap f).app a ≫ L.extendedTruncationTowerι.app a =
      K.extendedTruncationTowerι.app a ≫ f := by
  induction a using WithBotTop.rec with
  | bot => exact (isZero_zero _).eq_of_src _ _
  | coe a =>
    exact HomologicalComplex.ιTruncLE_naturality f (ComplexShape.embeddingUpIntLE (a - 1))
  | top =>
    change f ≫ 𝟙 L = 𝟙 K ≫ f
    simp only [Category.comp_id, Category.id_comp]

instance extendedTruncationTowerι_app_mono (K : CochainComplex C ℤ) (a : EInt) :
    Mono (K.extendedTruncationTowerι.app a) := by
  induction a using WithBotTop.rec with
  | bot => change Mono (0 : 0 ⟶ K); infer_instance
  | coe a => exact extendedTruncationInclusion_mono K (a - 1)
  | top => change Mono (𝟙 K); infer_instance

@[reassoc]
theorem extendedTruncationTower_map_ι (K : CochainComplex C ℤ)
    {a b : EInt} (f : a ⟶ b) :
    K.extendedTruncationTower.map f ≫ K.extendedTruncationTowerι.app b =
      K.extendedTruncationTowerι.app a := by
  have h := K.extendedTruncationTowerι.naturality f
  change K.extendedTruncationTower.map f ≫ K.extendedTruncationTowerι.app b =
    K.extendedTruncationTowerι.app a ≫ 𝟙 K at h
  exact h.trans (Category.comp_id _)

end CochainComplex
