/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps
import all WeilConjectures.AlgebraicGeometry.AffineBasePieceTensorBaseChangeInstance

/-!
# Tensor-spectrum comparison for an open affine triple

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A compatible spectrum model of an open affine triple remains a model after
base change along a map whose inverse image of the base open has a spectrum model.
The source open in the base change is the inverse image of the chosen source open.

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph; Schemes,
Tags 01JR and 01I4 (open fibre products and affine fibre products). -/
theorem affine_triple_tensor_base_change
    {S : Scheme.{u}} (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    (W₀ : S.Opens) (V₀ : Y₀.left.Opens) (U₀ : X₀.left.Opens)
    (hVW : V₀ ≤ Y₀.hom ⁻¹ᵁ W₀) (hUV : U₀ ≤ f₀.left ⁻¹ᵁ V₀)
    (R B C : CommRingCat.{u}) [Algebra R B] [Algebra R C]
    (φ : B →ₐ[R] C)
    (e0 : W₀.toScheme ≅ Spec R) (eB : V₀.toScheme ≅ Spec B)
    (eC : U₀.toScheme ≅ Spec C)
    (hB : eB.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Y₀.hom.resLE W₀ V₀ hVW ≫ e0.hom)
    (hC : eC.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
      f₀.left.resLE V₀ U₀ hUV ≫ eB.hom)
    (T : Scheme.{u}) (t : T ⟶ S) (A : CommRingCat.{u}) [Algebra R A]
    (eA : (t ⁻¹ᵁ W₀).toScheme ≅ Spec A)
    (ht : t.resLE W₀ _ le_rfl ≫ e0.hom =
      eA.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    let F := ((Over.pullback t).map f₀).left
    ∃ (V : ((Over.pullback t).obj Y₀).left.Opens)
      (U : ((Over.pullback t).obj X₀).left.Opens) (h : U ≤ F ⁻¹ᵁ V),
      U = (pullback.fst X₀.hom t) ⁻¹ᵁ U₀ ∧
      Nonempty (Arrow.mk (F.resLE V U h) ≅
        Arrow.mk (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (Algebra.ofId A A) φ).toRingHom))) := by
  let F := ((Over.pullback t).map f₀).left
  let VT := (pullback.fst Y₀.hom t) ⁻¹ᵁ V₀
  let UT := (pullback.fst X₀.hom t) ⁻¹ᵁ U₀
  let WT := t ⁻¹ᵁ W₀
  let g := f₀.left.resLE V₀ U₀ hUV
  let q := Y₀.hom.resLE W₀ V₀ hVW
  let s := t.resLE W₀ WT le_rfl
  have hUW : U₀ ≤ X₀.hom ⁻¹ᵁ W₀ := by
    rw [← Over.w f₀, Scheme.Hom.comp_preimage]
    exact hUV.trans (f₀.left.preimage_mono hVW)
  have hVT : VT ≤ (pullback.snd Y₀.hom t) ⁻¹ᵁ WT := by
    dsimp [VT, WT]
    rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
    exact (pullback.fst Y₀.hom t).preimage_mono hVW
  have hUT : UT ≤ (pullback.snd X₀.hom t) ⁻¹ᵁ WT := by
    dsimp [UT, WT]
    rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
    exact (pullback.fst X₀.hom t).preimage_mono hUW
  have hUVT : UT ≤ F ⁻¹ᵁ VT := by
    dsimp [VT]
    rw [← Scheme.Hom.comp_preimage]
    simp only [F, Over.pullback_map_left, pullback.lift_fst]
    rw [Scheme.Hom.comp_preimage]
    exact (pullback.fst X₀.hom t).preimage_mono hUV
  have hBpb := Scheme.Hom.isPullback_resLE
    (IsPullback.of_hasPullback Y₀.hom t) (le_rfl : WT ≤ t ⁻¹ᵁ W₀) hVW
    (UY := VT) (inf_eq_left.mpr hVT).symm
  have hCpb := Scheme.Hom.isPullback_resLE
    (IsPullback.of_hasPullback X₀.hom t) (le_rfl : WT ≤ t ⁻¹ᵁ W₀) hUW
    (UY := UT) (inf_eq_left.mpr hUT).symm
  have hq : X₀.hom.resLE W₀ U₀ hUW = g ≫ q := by
    rw [← cancel_mono W₀.ι]
    simp [g, q, Category.assoc, Scheme.Hom.resLE_comp_ι_assoc, Over.w]
  rw [hq] at hCpb
  let fT := F.resLE VT UT hUVT
  have hfst : fT ≫ (pullback.fst Y₀.hom t).resLE V₀ VT le_rfl =
      (pullback.fst X₀.hom t).resLE U₀ UT le_rfl ≫ g := by
    rw [← cancel_mono V₀.ι]
    simp [fT, g, F, Category.assoc, Scheme.Hom.resLE_comp_ι_assoc,
      Over.pullback_map_left]
  have hsnd : fT ≫ (pullback.snd Y₀.hom t).resLE WT VT hVT =
      (pullback.snd X₀.hom t).resLE WT UT hUT := by
    rw [← cancel_mono WT.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    dsimp [fT]
    rw [Scheme.Hom.resLE_comp_ι_assoc]
    simp [F, Over.pullback_map_left]
  let p := pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _) (by simp) (by simp)
  have ep : Arrow.mk fT ≅ Arrow.mk p := by
    refine Arrow.isoMk hCpb.isoPullback hBpb.isoPullback ?_
    apply pullback.hom_ext
    · dsimp [p]
      simp only [Category.assoc, pullback.lift_fst]
      rw [reassoc_of% hCpb.isoPullback_hom_fst, hBpb.isoPullback_hom_fst]
      exact hfst.symm
    · dsimp [p]
      simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [hCpb.isoPullback_hom_snd, hBpb.isoPullback_hom_snd]
      exact hsnd.symm
  obtain ⟨et⟩ := tensor_pullback_arrow g q s R A B C φ e0 eB eC eA
    hB.symm hC.symm ht
  exact ⟨VT, UT, hUVT, rfl, ⟨ep ≪≫ et⟩⟩

end AlgebraicGeometry
