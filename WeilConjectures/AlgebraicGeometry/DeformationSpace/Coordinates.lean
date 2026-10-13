/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# Étale coordinates on the deformation to the normal cone

Let `g : V ⟶ B` be smooth of relative dimension `d` with a closed section `s`. Étale-locally on
`B` there are coordinates `x₁, …, x_d` on `V` over `B` in which `s` is the origin, and on the
chart `u_i = x_i / t` the deformation space `D_s V` is étale over `𝔸^d_{𝔸¹_B}`, with the section
`s̃` going to the zero section (blueprint `sk-lem-geometry` (2), (4), (5)). Together with the
constructions of `WeilConjectures.AlgebraicGeometry.DeformationToNormalCone`, this gives the
deformation datum of blueprint `sk-lem-geometry`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V B : Scheme.{u}}

namespace Scheme.Hom

open AffineZariskiSite

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

**Existence of the deformation to the normal cone.** Let `g : V ⟶ B` be smooth of pure
relative dimension `d` with a closed section `s`, and let `N_s ⟶ B` be the normal cone of `s`
(`AlgebraicGeometry.Scheme.Hom.normalConeData`) with its zero section. Then the deformation
datum of `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData` exists, with fibre `N_s`
over `t = 0`: the deformation space is the relative spectrum `D_s V = Spec_V 𝒪_V[t, I t⁻¹]` of the
extended Rees algebra of the ideal `I` of `s`. Its fibre over `t = 1` is `V` and over `t = 0` the
normal cone, over the punctured line it is `V ×_B 𝔾_{m,B}`, and `g̃` is smooth of relative
dimension `d`. As `g` is separated and quasi-compact over a quasi-compact quasi-separated base,
`g̃` is separated and compactifiable.

TODO: the étale-local coordinates (`exists_etale_coordinates`, clauses (2), (4) and (5)) are not
yet constructed; the charts of `smoothOfRelativeDimension_deformationSpaceProj` are their
Zariski-local form. -/
theorem nonempty_deformationToNormalConeData (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] [CompactSpace B]
    [QuasiSeparatedSpace B] (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    Nonempty (DeformationToNormalConeData d g s (normalConeData d hs)) :=
  have := smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have hm : ((puncturedLine B).ι ≫ s.deformationSpaceSection) ≫ deformationSpaceProj g s =
      𝟙 _ ≫ (puncturedLine B).ι := by
    rw [Category.assoc, deformationSpaceSection_deformationSpaceProj hs, Category.comp_id,
      Category.id_comp]
  have P := isPullback_deformationSpaceGeneric g s
  ⟨{ scheme := s.ker.deformationSpace
     proj := deformationSpaceProj g s
     sect := s.deformationSpaceSection
     sect_comp_proj := deformationSpaceSection_deformationSpaceProj hs
     smoothOfRelativeDimension_proj := this
     isSeparated_proj := inferInstance
     hasCompactification_proj := hasCompactification_deformationSpaceProj g s d hs
     oneFibre := deformationSpaceOneFibre g s
     isPullback_oneFibre := isPullback_deformationSpaceOneFibre g s
     comp_oneFibre := comp_deformationSpaceOneFibre hs
     zeroFibre := s.ker.normalConeToDeformationSpace
     isPullback_zeroFibre := isPullback_normalConeToDeformationSpace g s
     comp_zeroFibre := normalConeZeroSection_comp_normalConeToDeformationSpace
     puncturedLine := puncturedLine B
     coe_puncturedLine := coe_puncturedLine B
     generic := deformationSpaceGeneric g s
     isPullback_generic := P
     exists_sect_generic := ⟨P.lift _ _ hm, by
       rw [← deformationSpaceGeneric_toBase g s, P.lift_fst_assoc, Category.assoc,
         deformationSpaceSection_toBase, Category.assoc], P.lift_snd _ _ _, P.lift_fst _ _ _⟩
     exists_etale_coordinates := sorry }⟩


end Scheme.Hom

end AlgebraicGeometry
