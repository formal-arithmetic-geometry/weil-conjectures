/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DeformationIso

/-!
# Transport of the DNC isomorphism

The DNC isomorphism `α_{g,s} : 𝒞(g, s) ≅ 𝒞(π_N, 0_N)` of a deformation datum `D` is the inverse
of the restriction to `t = 0` of the constancy comparison `χ_{g,s} : F ≅ a^* 𝒞(g, s)` of the
family object, which is the unique comparison that is the identity at `t = 1`. Hence any
identification `ε : F' ≅ F` of the family objects of two deformation data over the same base
transports `α_{g',s'}` to `α_{g,s}`, along the identifications of the fibres at `t = 1` and
`t = 0` induced by `ε`: transported along `ε`, `χ_{g',s'}` is again a comparison that is the
identity at `t = 1`, so it is `χ_{g,s}`.

This is the uniqueness argument of blueprint `lemma-naturality-under-base-change-etale` (2):
there `ε` is the identification `s̃'^* ω_{g̃'} ≅ s̃^* ω_{g̃}` of family objects obtained by
composing adjunctions for the étale map of deformation spaces, whose restrictions to `t = 1` and
`t = 0` are the identifications for the original pairs and for the normal cones.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.familyObjectIso_eq_of_iso`: the
  constancy comparison is transported by an identification of family objects.
- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.sectionInvariantIsoOfFibreIso_trans`:
  so is the DNC isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
  [HasTateTwist.IsNormalized Λ] {V V' B : Scheme.{u}} {d d' : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)
  {g' : V' ⟶ B} {s' : B ⟶ V'} {N' : NormalConeData d' s'}
  (D' : DeformationToNormalConeData d' g' s' N') [HasInvertibleExponent Λ B]
  [HasCompactification g] [HasCompactification g'] {k : Type u} [Field k]
  (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact D.proj]
  [QuasiCompact D'.proj]

/-- The constancy comparison `χ_{g,s}` normalized against `θ₁` is the transport, along an
identification `ε : F' ≅ F` of family objects and an identification `ι₁ : 𝒞(g', s') ≅ 𝒞(g, s)`
compatible with `ε` at `t = 1`, of the constancy comparison `χ_{g',s'}` normalized against
`θ₁'`. -/
theorem familyObjectIso_eq_of_iso (ε : D'.familyObject Λ ≅ D.familyObject Λ)
    (θ₁ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (θ₁' : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D'.familyObject Λ) ≅ sectionInvariant Λ g' s')
    (ι₁ : sectionInvariant Λ g' s' ≅ sectionInvariant Λ g s)
    (h₁ : θ₁'.hom ≫ ι₁.hom =
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map ε.hom ≫
        θ₁.hom) :
    D.familyObjectIso Λ aB θ₁ = ε.symm ≪≫ D'.familyObjectIso Λ aB θ₁' ≪≫
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).mapIso ι₁ := by
  refine (D.eq_familyObjectIso Λ aB θ₁ _ ?_).symm
  have hn := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
    (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).hom.naturality ι₁.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    hn]
  rw [reassoc_of% (D'.leftDerivedUpperStar_map_familyObjectIso_hom_comp Λ aB θ₁'), h₁,
    ← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp

variable [HasCompactification N.proj] [HasCompactification N'.proj]

/-- Blueprint `lemma-naturality-under-base-change-etale--7`: *identifications induced by the
family objects carry `α_{g',s'}` to `α_{g,s}`.* Let `ε : F' ≅ F` identify the family objects of
two deformation data over the same base, and let `ι₁ : 𝒞(g', s') ≅ 𝒞(g, s)` and
`ι₀ : 𝒞(π_{N'}, 0) ≅ 𝒞(π_N, 0)` be the identifications of the fibres at `t = 1` and `t = 0`
induced by `ε` through the fibre identifications `θ₁, θ₀` and `θ₁', θ₀'`. Then the DNC
isomorphisms satisfy `α_{g',s'} ≫ ι₀ = ι₁ ≫ α_{g,s}`. -/
theorem sectionInvariantIsoOfFibreIso_trans (ε : D'.familyObject Λ ≅ D.familyObject Λ)
    (θ₁ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (θ₀ : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection)
    (θ₁' : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D'.familyObject Λ) ≅ sectionInvariant Λ g' s')
    (θ₀' : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D'.familyObject Λ) ≅ sectionInvariant Λ N'.proj N'.zeroSection)
    (ι₁ : sectionInvariant Λ g' s' ≅ sectionInvariant Λ g s)
    (ι₀ : sectionInvariant Λ N'.proj N'.zeroSection ≅ sectionInvariant Λ N.proj N.zeroSection)
    (h₁ : θ₁'.hom ≫ ι₁.hom =
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map ε.hom ≫
        θ₁.hom)
    (h₀ : θ₀'.hom ≫ ι₀.hom =
      (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map ε.hom ≫
        θ₀.hom) :
    D'.sectionInvariantIsoOfFibreIso Λ aB θ₁' θ₀' ≪≫ ι₀ =
      ι₁ ≪≫ D.sectionInvariantIsoOfFibreIso Λ aB θ₁ θ₀ := by
  have hn := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B)).hom.naturality ι₁.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Iso.symm_eq_iff]
  ext
  simp only [sectionInvariantIsoOfFibreIso, familyObjectIso_eq_of_iso Λ D D' aB ε θ₁ θ₁' ι₁ h₁,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc, hn]
  have h₀' : ι₀.inv ≫ θ₀'.inv = θ₀.inv ≫
      (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map ε.inv := by
    rw [Iso.inv_comp_eq]
    refine Iso.inv_ext ?_
    rw [reassoc_of% h₀]
    simp
  rw [reassoc_of% h₀', Iso.hom_inv_id, Category.comp_id]

end Scheme.Hom.DeformationToNormalConeData

end AlgebraicGeometry
