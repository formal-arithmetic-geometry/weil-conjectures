/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.EtaleLowerShriekAffine
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.MayerVietoris

/-!
# Extensions by zero along quasi-compact separated étale maps are constructible

Stacks 03SA for `Λ`: the extension by zero `v_! Λ` along a quasi-compact separated étale map
`v : V ⟶ Y` to an affine scheme is constructible
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_lowerShriekUnit_of_isAffine`), by induction on
the number of affine opens covering `V`, using Mayer–Vietoris
(`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerShriekUnit_of_sup`) and the affine case.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The induction on the number of affine opens covering the source. -/
theorem isConstructibleSheaf_lowerShriekUnit_of_isAffine_of_cover {Y : Scheme.{u}} [IsAffine Y]
    (n : ℕ) : ∀ {V : Scheme.{u}} (v : V ⟶ Y) [Etale v] [IsSeparated v]
      (U : Fin (n + 1) → V.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ →
      IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) v inferInstance) := by
  induction n with
  | zero =>
    intro V v _ _ U hU hcov
    have h0 : U 0 = ⊤ := by
      rw [← hcov]
      exact le_antisymm (le_iSup U 0) (iSup_le fun i ↦ by
        rw [(Fin.ext (by have := i.2; omega) : i = 0)])
    have : IsAffine V := by
      have := hU 0
      rw [h0] at this
      have : IsAffine (⊤ : V.Opens).toScheme := this
      exact .of_isIso V.topIso.inv
    exact isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_isAffine v _
  | succ n ih =>
    intro V v _ _ U hU hcov
    let V₁ : V.Opens := ⨆ i : Fin (n + 1), U i.castSucc
    let V₂ : V.Opens := U (Fin.last _)
    have hV : V₁ ⊔ V₂ = ⊤ := by
      refine eq_top_iff.mpr (hcov.symm.le.trans (iSup_le fun i ↦ ?_))
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i).trans le_sup_left
    have hsep := isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal v))
      ⊤ (isAffineOpen_top Y)
    refine Etale.isConstructibleSheaf_lowerShriekUnit_of_sup v inferInstance V₁ V₂ hV ?_ ?_ ?_
    · refine ih (V₁.ι ≫ v) (fun i ↦ V₁.ι ⁻¹ᵁ U i.castSucc)
        (fun i ↦ (hU _).preimage_of_isOpenImmersion _ ?_) ?_
      · rw [Scheme.Opens.opensRange_ι]
        exact le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i
      · rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
    · have : IsAffine V₂ := hU _
      exact isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_isAffine _ _
    · refine ih ((V₁ ⊓ V₂).ι ≫ v) (fun i ↦ (V₁ ⊓ V₂).ι ⁻¹ᵁ (U i.castSucc ⊓ V₂))
        (fun i ↦ (hsep _ le_top _ le_top (hU _) (hU _)).preimage_of_isOpenImmersion _ ?_) ?_
      · rw [Scheme.Opens.opensRange_ι]
        exact inf_le_inf_right _ (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i)
      · rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq, Scheme.Opens.ι_preimage_self]

end AlgebraicGeometry.Scheme
