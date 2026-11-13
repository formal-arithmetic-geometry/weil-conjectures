/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Uniqueness of normalized diagonal conormal derivations on sections

Two diagonal conormal derivations normalized by the kernel class map agree on the
sections over every open (Stacks Project, Tag 08S2). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- Normalized diagonal conormal derivations agree on sections of every open.
Source: Stacks Project, Tag 08S2. -/
theorem diagonalConormal_affine_sections_unique (f : X ⟶ S)
    (U : X.Opens)
    (D₁ D₂ : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf)
    (h₁ : IsDiagonalConormalDerivation f D₁)
    (h₂ : IsDiagonalConormalDerivation f D₂) :
    ∀ a : Γ(X, U), D₁.d (X := op U) a = D₂.d (X := op U) a := by
  let δ := pullback.diagonal f
  let W := (pullback.fst f f) ⁻¹ᵁ U ⊓ (pullback.snd f f) ⁻¹ᵁ U
  have hδ : U ≤ δ ⁻¹ᵁ W := by
    change U ≤ (pullback.diagonal f) ⁻¹ᵁ
      ((pullback.fst f f) ⁻¹ᵁ U ⊓ (pullback.snd f f) ⁻¹ᵁ U)
    simp only [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem]
    exact le_rfl
  intro a
  let φ := SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom
  let b := (pullback.snd f f).appLE U W inf_le_right a -
    (pullback.fst f f).appLE U W inf_le_left a
  have hb : (SheafOfModules.evaluation (pullback f f).ringCatSheaf (op W)).map φ b = 0 := by
    change δ.app W b = 0
    dsimp only [b]
    rw [map_sub]
    have hsnd : (pullback.snd f f).appLE U W inf_le_right ≫ δ.app W =
        (pullback.fst f f).appLE U W inf_le_left ≫ δ.app W := by
      rw [δ.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        Scheme.Hom.appLE_comp_appLE]
      simp [δ]
    exact sub_eq_zero.mpr (ConcreteCategory.congr_hom hsnd a)
  have hb' : b ∈ Set.range
      ((SheafOfModules.evaluation (pullback f f).ringCatSheaf (op W)).map (kernel.ι φ)) := by
    rw [Scheme.Modules.range_map_kernelι]
    exact hb
  obtain ⟨s, hs⟩ := hb'
  exact (h₁ U W inf_le_left inf_le_right hδ a s hs).trans
    (h₂ U W inf_le_left inf_le_right hδ a s hs).symm

end AlgebraicGeometry
