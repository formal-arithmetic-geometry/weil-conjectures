/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeNaturality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf

/-!
# Section invariants along étale maps of pairs

Let `g : V ⟶ B` be smooth of relative dimension `d` with a section `s`, and let `e : V' ⟶ V` be
étale with a section `s'` of `e ≫ g` such that `s' ≫ e = s`. Composing the exceptional inverse
images `R(e ≫ g)^! ≅ Re^! Rg^!` and using `Re^! ≅ Le^*` on `D^b_{ctf}` for the étale `e`
identifies the section invariants

`𝒞(e ≫ g, s') = Ls'^* R(e ≫ g)^! Λ ≅ Ls'^* Le^* Rg^! Λ ≅ Ls^* ω_g = 𝒞(g, s)`.

For an étale map of pairs (`e⁻¹(s(B)) = s'(B)`), the induced map of normal cones is an
isomorphism over `B` respecting the zero sections
(`AlgebraicGeometry.Scheme.Hom.isIso_normalConeMap_of_etale`), so the same argument identifies
the section invariants of the normal cones. These are the identifications of blueprint
`lemma-naturality-under-base-change-etale` (2). The comparison of exceptional inverse images is
only known to exist in this framework, so the identifications are recorded as existence
statements.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_of_etale`: `𝒞(e ≫ g, s') ≅ 𝒞(g, s)`.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone_of_etale`:
  `𝒞(π_{N_{s'}}, 0) ≅ 𝒞(π_{N_s}, 0)` for an étale map of pairs.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (d : ℕ)

/-- Blueprint `lemma-naturality-under-base-change-etale--5`, the identification of section
invariants: for `g` smooth of relative dimension `d`, an étale `e : V' ⟶ V` and sections `s` of
`g` and `s'` of `g' = e ≫ g` with `s' ≫ e = s`, composing the adjunctions `Re_! ⊣ Re^!` and
`Rg_! ⊣ Rg^!` identifies `𝒞(g', s') = Ls'^* ω_{g'} ≅ Ls^* ω_g = 𝒞(g, s)`. -/
theorem nonempty_iso_sectionInvariant_of_etale {V' V B : Scheme.{u}} (e : V' ⟶ V)
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] {g' : V' ⟶ B}
    [HasCompactification g'] [QuasiCompact g'] (hg : e ≫ g = g') [HasInvertibleExponent Λ B]
    {s : B ⟶ V} {s' : B ⟶ V'} (hs : s' ≫ e = s) :
    Nonempty (sectionInvariant Λ g' s' ≅ sectionInvariant Λ g s) := by
  have : HasInvertibleExponent Λ V := .of_hom g
  have : HasInvertibleExponent Λ V' := .of_hom g'
  have : HasCompactification (e ≫ g) := .of_eq hg.symm
  have : QuasiCompact (e ≫ g) := by rw [hg]; infer_instance
  obtain ⟨e₀⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq Λ hg
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ e g
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_obj_of_etale Λ e _
    (boundedConstructibleFiniteTor_dualizingComplex Λ d g)
  exact ⟨(L((s')^*[ModuleCat.{u + 1} Λ])).mapIso ((e₀.app _).symm ≪≫ e₁.app _ ≪≫ e₂) ≪≫
    ((leftDerivedUpperStarComp _ s' e s hs.symm).app _).symm⟩

variable {V' V B : Scheme.{u}} {g : V ⟶ B} {s : B ⟶ V} (e : V' ⟶ V) (s' : B ⟶ V')

/-- Blueprint `lemma-naturality-under-base-change-etale--6`: for an étale map of pairs, that is
`e : V' ⟶ V` étale and a closed section `s'` of `e ≫ g` with `s' ≫ e = s` and
`e⁻¹(s(B)) = s'(B)` scheme-theoretically, the section invariants of the zero sections of the
normal cones are identified, `𝒞(π_{N_{s'}}, 0) ≅ 𝒞(π_{N_s}, 0)`: the morphism of normal cones
is an isomorphism over `B` carrying zero section to zero section
(`AlgebraicGeometry.Scheme.Hom.isIso_normalConeMap_of_etale`), and an isomorphism is étale. -/
theorem nonempty_iso_sectionInvariant_normalCone_of_etale [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) [_root_.AlgebraicGeometry.Etale e]
    [IsClosedImmersion s'] (hes : s' ≫ e = s) (hker : s.ker.comap e = s'.ker)
    [HasCompactification (Hom.normalConeProj g s)]
    [HasCompactification (Hom.normalConeProj (e ≫ g) s')]
    [QuasiCompact (Hom.normalConeProj (e ≫ g) s')] [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ (Hom.normalConeProj (e ≫ g) s') s'.normalConeZeroSection ≅
      sectionInvariant Λ (Hom.normalConeProj g s) s.normalConeZeroSection) := by
  have := Hom.isIso_normalConeMap_of_etale e s' hs hes hker
  have : HasCompactification (IdealSheafData.normalConeMap e s.ker s'.ker
      (Hom.map_siteIdeal_ker_le_of_comap_eq e s' hker)) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have : SmoothOfRelativeDimension d (Hom.normalConeProj g s) :=
    (Hom.normalConeData d hs).smoothOfRelativeDimension_proj
  exact nonempty_iso_sectionInvariant_of_etale Λ d _ (Hom.normalConeProj g s)
    (Hom.normalConeMap_normalConeProj e s' hker)
    (Hom.normalConeZeroSection_normalConeMap e s' hes hker)

end AlgebraicGeometry.Etale
