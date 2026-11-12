/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap

/-!
# Naturality of the normal cone and the deformation space of a section

Let `g : V ⟶ B` be smooth with a closed section `s`, with normal cone `N_s` and deformation space
`𝒟_s V` (`AlgebraicGeometry.Scheme.Hom.deformationSpaceProj`). This file proves the geometric
part of blueprint `lemma-naturality-under-base-change-etale`.

* (1) For any `b : B' ⟶ B`, the normal cone of the base-changed section is the base change of the
  normal cone, `N_{s'} ≅ N_s ×_B B'`: it is the fibre over `t = 0` of the deformation space,
  which commutes with base change
  (`AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange`).
* (2) For an étale `e : V' ⟶ V` and a section `s'` with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)`
  scheme-theoretically, the map of normal cones `N_{s'} ⟶ N_s`, induced by the maps of
  associated graded algebras (hence linear), is an isomorphism, and the map of deformation spaces
  `𝒟_{s'} V' ⟶ 𝒟_s V` is étale: the deformation space commutes with the flat base change `e`
  (`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_deformationSpaceMap_of_flat`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_normalCone_baseChange`
- `AlgebraicGeometry.Scheme.Hom.isIso_normalConeMap_of_etale`
- `AlgebraicGeometry.Scheme.Hom.etale_deformationSpaceMap_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

section BaseChange

variable {V B B' : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V) (hs : s ≫ g = 𝟙 B) (b : B' ⟶ B)

/-- Blueprint `lemma-naturality-under-base-change-etale` (1): *the normal cone commutes with base
change.* For `g : V ⟶ B` smooth of relative dimension `d` with a closed section `s`, and any
`b : B' ⟶ B`, the normal cone of the base-changed section `s'` of `g' : V ×_B B' ⟶ B'` is the
base change of the normal cone of `s`,

`N_{s'} = N_s ×_B B'`,

compatibly with the zero sections. -/
theorem exists_isPullback_normalCone_baseChange (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] :
    ∃ ψ : (baseChangeSection g s hs b).ker.normalCone ⟶ s.ker.normalCone,
      IsPullback ψ (normalConeProj (pullback.snd g b) (baseChangeSection g s hs b))
        (normalConeProj g s) b ∧
      (baseChangeSection g s hs b).normalConeZeroSection ≫ ψ = b ≫ s.normalConeZeroSection := by
  sorry

end BaseChange

section Etale

variable {V V' B : Scheme.{u}} (e : V' ⟶ V) (s : B ⟶ V) (s' : B ⟶ V')

/-- For `s' ≫ e = s`, the ideal of `s` pulls back into the ideal of `s'`. -/
lemma map_siteIdeal_ker_le_of_comp_eq (hs : s' ≫ e = s) ⦃U' : V'.AffineZariskiSite⦄
    ⦃U : V.AffineZariskiSite⦄ (hU : U'.1 ≤ e ⁻¹ᵁ U.1) :
    (s.ker.siteIdeal U).map (e.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U' :=
  (IdealSheafData.map_siteIdeal_le_comap e s.ker hU).trans
    ((show s.ker.comap e ≤ s'.ker by rw [IdealSheafData.comap_le_ker_iff, hs]) ⟨U'.1, U'.2⟩)

/-- Blueprint `lemma-naturality-under-base-change-etale` (4): let `e : V' ⟶ V` be étale and `s'`
a section with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)` scheme-theoretically. Then the induced map
of normal cones `N_{s'} ⟶ N_s` (`AlgebraicGeometry.Scheme.IdealSheafData.normalConeMap`, induced
by the maps of associated graded algebras, hence linear) is an isomorphism. -/
theorem isIso_normalConeMap_of_etale [Etale e] [IsClosedImmersion s] (hs : s' ≫ e = s)
    (he : IsPullback s' (𝟙 B) e s) :
    IsIso (IdealSheafData.normalConeMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comp_eq e s s' hs)) := by
  sorry

/-- Blueprint `lemma-naturality-under-base-change-etale` (5): let `e : V' ⟶ V` be étale and `s'`
a section with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)` scheme-theoretically. Then the induced map
of deformation spaces `𝒟_{s'} V' ⟶ 𝒟_s V`
(`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceMap`) is étale. -/
theorem etale_deformationSpaceMap_of_etale [Etale e] [IsClosedImmersion s] (hs : s' ≫ e = s)
    (he : IsPullback s' (𝟙 B) e s) :
    Etale (IdealSheafData.deformationSpaceMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comp_eq e s s' hs)) := by
  sorry

end Etale

end AlgebraicGeometry.Scheme.Hom
