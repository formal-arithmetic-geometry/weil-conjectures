/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# Base change of the normal cone of a section

Let `g : V ⟶ B` be smooth of relative dimension `d` with a closed section `s`, and let
`b : B' ⟶ B`. The base change `g' : V ×_B B' ⟶ B'` has the section `s' = (b ≫ s, 𝟙)`. The normal
cone of `s'` is the base change of the normal cone of `s`,

`N_{s'} = N_s ×_B B'`,

compatibly with the zero sections. It is the fibre over `t = 0` of the deformation space, and
the deformation space commutes with base change
(`AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_normalCone_baseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {V B B' : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V) (hs : s ≫ g = 𝟙 B) (b : B' ⟶ B)

/-- **Base change of the normal cone.** For `g : V ⟶ B` smooth of relative dimension `d` with a
closed section `s`, and any `b : B' ⟶ B`, the normal cone of the base-changed section
`s' = (b ≫ s, 𝟙)` of `g' : V ×_B B' ⟶ B'` is the base change of the normal cone of `s`,
`N_{s'} = N_s ×_B B'`, compatibly with the zero sections. -/
theorem exists_isPullback_normalCone_baseChange (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] :
    ∃ φ : (baseChangeSection g s hs b).ker.normalCone ⟶ s.ker.normalCone,
      IsPullback φ (normalConeProj (pullback.snd g b) (baseChangeSection g s hs b))
        (normalConeProj g s) b ∧
      (baseChangeSection g s hs b).normalConeZeroSection ≫ φ = b ≫ s.normalConeZeroSection := by
  obtain ⟨φD, hD, hsD⟩ := exists_isPullback_deformationSpace_baseChange g s hs b d
  have hN := isPullback_normalConeToDeformationSpace g s
  have hbig := (isPullback_normalConeToDeformationSpace (pullback.snd g b)
    (baseChangeSection g s hs b)).paste_horiz hD
  rw [AffineSpace.zeroSection_comp_map] at hbig
  have hw := hbig.w.trans (Category.assoc _ _ _).symm
  rw [← hN.lift_fst (_ ≫ φD) (_ ≫ b) hw] at hbig
  refine ⟨hN.lift _ _ hw, hbig.of_right (hN.lift_snd _ _ hw) hN, hN.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hN.lift_fst,
      reassoc_of% normalConeZeroSection_comp_normalConeToDeformationSpace,
      hsD, reassoc_of% AffineSpace.zeroSection_comp_map, Category.assoc,
      normalConeZeroSection_comp_normalConeToDeformationSpace]
  · rw [Category.assoc, hN.lift_snd, reassoc_of% normalConeZeroSection_normalConeProj
      (baseChangeSection_snd g s hs b), Category.assoc, normalConeZeroSection_normalConeProj hs,
      Category.comp_id]

end AlgebraicGeometry.Scheme.Hom
