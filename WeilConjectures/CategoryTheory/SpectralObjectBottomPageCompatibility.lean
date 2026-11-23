/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SpectralObjectBottomPageMap
import WeilConjectures.CategoryTheory.SpectralObjectBottomPageIntervalCompatibility

/-! # Compatibility of a bottom-page map with passage to homology

Source: Stacks Project, Tags 012K and 015N.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

/-- The cycles-to-homology square commutes with the bottom-page map to the abutment.
Source: Stacks Project, Tags 012K and 015N. -/
theorem bottomPageMap_compatibility
    {C : Type u} [Category.{v} C] [Abelian C]
    (Y : SpectralObject C EInt) [Y.IsFirstQuadrant]
    (p : ℕ) (r : ℤ) (hr : 2 ≤ r) :
    (Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0) ≫ Y.bottomPageMap p r hr =
      (Y.E₂SpectralSequenceNat.page r hr).homologyπ (p, 0) ≫
        (Y.E₂SpectralSequenceNat.iso r (r + 1) (p, 0) rfl hr).hom ≫
          Y.bottomPageMap p (r + 1) (by omega) := by
  have h := Y.bottomPage_interval_compatibility p r hr
  dsimp only at h
  dsimp only [bottomPageMap]
  have hi (s : ℤ) (hs : 2 ≤ s) :=
    Y.isIso_H_map_twoδ₁Toδ₀' p (p + 1) rfl ⊥ (0 : ℤ) (s - 1 : ℤ)
      bot_le (WithBotTop.coe_le_coe.2 (by omega))
      (Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl _)
      (Y.isZero₁_of_isFirstQuadrant _ _ _ le_rfl _)
  have := hi r hr
  have := hi (r + 1) (by omega)
  let f := (Y.H p).map (twoδ₁Toδ₀' (⊥ : EInt) ((0 : ℤ) : EInt) ((r - 1 : ℤ) : EInt)
    bot_le (WithBotTop.coe_le_coe.2 (by omega)))
  let f' := (Y.H p).map (twoδ₁Toδ₀' (⊥ : EInt) ((0 : ℤ) : EInt) ((r + 1 - 1 : ℤ) : EInt)
    bot_le (WithBotTop.coe_le_coe.2 (by omega)))
  let g := (Y.H p).map (twoδ₂Toδ₁' ((0 : ℤ) : EInt) (r - 1 : ℤ) (r + 1 - 1 : ℤ)
    (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega)))
  let g' := (Y.H p).map (twoδ₂Toδ₁' (⊥ : EInt) (r - 1 : ℤ) (r + 1 - 1 : ℤ)
    bot_le (WithBotTop.coe_le_coe.2 (by omega)))
  let t := (Y.H p).map (twoδ₂Toδ₁' (⊥ : EInt) (r - 1 : ℤ) ⊤ bot_le le_top)
  let t' := (Y.H p).map (twoδ₂Toδ₁' (⊥ : EInt) (r + 1 - 1 : ℤ) ⊤ bot_le le_top)
  have hsquare : f ≫ g = g' ≫ f' := by
    dsimp [f, g, g', f']
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  have htop : g' ≫ t' = t := by
    dsimp [g', t', t]
    rw [← Functor.map_comp]
    congr 1
  have htail : g ≫ inv f' ≫ t' = inv f ≫ t := by
    apply (cancel_epi f).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [hsquare]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, htop]
  dsimp only [g, f, f', t, t'] at htail
  have hh := congrArg (fun k => k ≫ inv f' ≫ t') h
  dsimp only [f', t'] at hh
  simp only [Category.assoc] at hh ⊢
  simpa only [Category.assoc, htail] using hh

end CategoryTheory.Abelian.SpectralObject
