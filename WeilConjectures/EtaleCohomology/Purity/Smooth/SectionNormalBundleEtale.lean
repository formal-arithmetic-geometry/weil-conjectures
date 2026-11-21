/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.Coordinates
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.EtaleMapOfPairs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DeformationIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantEtale

/-!
# The comparison of a section and its normal bundle along étale maps of pairs

Let `g : V ⟶ B` be smooth of relative dimension `d` with a closed section `s`, let `e : V' ⟶ V`
be étale and `s'` a section of `g' = e ≫ g` with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)`
scheme-theoretically. The induced map of normal cones `N_{s'} ⟶ N_s` is an isomorphism
(`AlgebraicGeometry.Scheme.Hom.isIso_normalConeMap_of_isPullback`), and composing adjunctions
gives identifications of section invariants

`𝒞(g', s') ≅ 𝒞(g, s)`, `𝒞(π_{N_{s'}}, 0) ≅ 𝒞(π_{N_s}, 0)`

(`AlgebraicGeometry.Etale.sectionInvariantEtaleIso`,
`AlgebraicGeometry.Etale.normalConeSectionInvariantEtaleIso`). They carry the comparison
`𝒞(g', s') ≅ 𝒞(π_{N_{s'}}, 0)` of the deformation to the normal cone to the comparison for
`(g, s)` (`AlgebraicGeometry.Etale.sectionInvariantEtaleIso_trans_sectionInvariantIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V' V B : Scheme.{u}} (g : V ⟶ B)
  (s : B ⟶ V) (e : V' ⟶ V) (s' : B ⟶ V') (he : IsPullback s' (𝟙 B) e s)

/-- The identification `𝒞(π_{N_{s'}}, 0) ≅ 𝒞(π_{N_s}, 0)` of the section invariants of the zero
sections of the normal cones, along the isomorphism `N_{s'} ≅ N_s` induced by an étale map of
pairs. -/
noncomputable def normalConeSectionInvariantEtaleIso [IsClosedImmersion s]
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification (Hom.normalConeProj g s)]
    [HasCompactification (Hom.normalConeProj (e ≫ g) s')]
    [QuasiCompact (Hom.normalConeProj (e ≫ g) s')] :
    sectionInvariant Λ (Hom.normalConeProj (e ≫ g) s') s'.normalConeZeroSection ≅
      sectionInvariant Λ (Hom.normalConeProj g s) s.normalConeZeroSection :=
  have := Hom.isIso_normalConeMap_of_isPullback s e s' he
  sectionInvariantEtaleIso Λ _ _ _ (Hom.normalConeMap_normalConeProj_of_isPullback s e s' he g)
    _ _ (Hom.normalConeZeroSection_normalConeMap_of_isPullback s e s' he)

include he in
/-- The section `s'` of `e ≫ g` is a section. -/
lemma comp_comp_eq_id_of_isPullback (hs : s ≫ g = 𝟙 B) : s' ≫ e ≫ g = 𝟙 B := by
  rw [← Category.assoc, he.w, Category.id_comp, hs]

/-- **The comparison of a section and its normal bundle is compatible with étale maps of
pairs.** The identifications `𝒞(g', s') ≅ 𝒞(g, s)` and `𝒞(π_{N_{s'}}, 0) ≅ 𝒞(π_{N_s}, 0)`
obtained by composing adjunctions carry the comparison `α_{g', s'}` of the deformation to the
normal cone to `α_{g, s}`. -/
theorem sectionInvariantEtaleIso_trans_sectionInvariantIso [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] (d : ℕ) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [CompactSpace B] [QuasiSeparatedSpace B] [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) [_root_.AlgebraicGeometry.Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e] [SmoothOfRelativeDimension d (e ≫ g)] [IsClosedImmersion s']
    [HasCompactification g] [HasCompactification (e ≫ g)]
    [HasCompactification (Hom.normalConeProj g s)]
    [HasCompactification (Hom.normalConeProj (e ≫ g) s')]
    [QuasiCompact (Hom.normalConeProj (e ≫ g) s')] {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    haveI : HasCompactification (Hom.normalConeData d hs).proj :=
      inferInstanceAs (HasCompactification (Hom.normalConeProj g s))
    haveI : HasCompactification
        (Hom.normalConeData d (comp_comp_eq_id_of_isPullback g s e s' he hs)).proj :=
      inferInstanceAs (HasCompactification (Hom.normalConeProj (e ≫ g) s'))
    haveI : QuasiCompact (Hom.deformationToNormalConeData d g s hs).proj :=
      inferInstanceAs (QuasiCompact (Hom.deformationSpaceProj g s))
    haveI : QuasiCompact
        (Hom.deformationToNormalConeData d (e ≫ g) s'
          (comp_comp_eq_id_of_isPullback g s e s' he hs)).proj :=
      inferInstanceAs (QuasiCompact (Hom.deformationSpaceProj (e ≫ g) s'))
    sectionInvariantEtaleIso Λ e g (e ≫ g) rfl s s' (by simpa using he.w) ≪≫
        (Hom.deformationToNormalConeData d g s hs).sectionInvariantIso Λ aB =
      (Hom.deformationToNormalConeData d (e ≫ g) s'
          (comp_comp_eq_id_of_isPullback g s e s' he hs)).sectionInvariantIso Λ aB ≪≫
        normalConeSectionInvariantEtaleIso Λ g s e s' he := by
  sorry

end Etale

end AlgebraicGeometry
