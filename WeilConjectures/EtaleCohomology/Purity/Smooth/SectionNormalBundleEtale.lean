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

/-- The base change compatibility `sectionInvariantEtaleIso_baseChange` of the identifications of
section invariants along étale maps, in the form of a commutative square of morphisms. -/
theorem sectionInvariantEtaleIso_baseChange_hom (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V' V B V₁' V₁ B₁ : Scheme.{u}} (e : V' ⟶ V)
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] (g : V ⟶ B) (g' : V' ⟶ B)
    (w : e ≫ g = g') [HasCompactification g] [HasCompactification g'] [QuasiCompact g']
    (b : B₁ ⟶ B) (e₁ : V₁' ⟶ V₁) [_root_.AlgebraicGeometry.Etale e₁] [HasCompactification e₁]
    (g₁ : V₁ ⟶ B₁) (g₁' : V₁' ⟶ B₁) (w₁ : e₁ ≫ g₁ = g₁') [HasCompactification g₁]
    [HasCompactification g₁'] [QuasiCompact g₁] [QuasiCompact g₁'] (v : V₁ ⟶ V) (v' : V₁' ⟶ V')
    (sq : IsPullback v g₁ g b) (sq' : IsPullback v' g₁' g' b) (hv : v' ≫ e = e₁ ≫ v)
    [IsIso (Etale.dualizingComplexBaseChangeMap Λ sq)]
    [IsIso (Etale.dualizingComplexBaseChangeMap Λ sq')]
    (s : B ⟶ V) (s' : B ⟶ V') (hs : s' ≫ e = s) (s₁ : B₁ ⟶ V₁) (s₁' : B₁ ⟶ V₁')
    (hs₁ : s₁' ≫ e₁ = s₁) (hv₁ : s₁ ≫ v = b ≫ s) (hv₁' : s₁' ≫ v' = b ≫ s') :
    (L((b)^*[ModuleCat.{u + 1} Λ])).map
        (Etale.sectionInvariantEtaleIso Λ e g g' w s s' hs).hom ≫
        (Etale.sectionInvariantBaseChangeIso Λ sq s s₁ hv₁).hom =
      (Etale.sectionInvariantBaseChangeIso Λ sq' s' s₁' hv₁').hom ≫
        (Etale.sectionInvariantEtaleIso Λ e₁ g₁ g₁' w₁ s₁ s₁' hs₁).hom := by
  rw [← Etale.sectionInvariantEtaleIso_baseChange Λ e g g' w b e₁ g₁ g₁' w₁ v v' sq sq' hv s s'
    hs s₁ s₁' hs₁ hv₁ hv₁']
  simp

end Etale

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

/-- *Naturality of the DNC isomorphism under étale maps of pairs*, for arbitrary deformation
data. Let `e : V' ⟶ V` be étale with `g' = e ≫ g` and `s' ≫ e = s`, and let `D'` be a
deformation datum for `(g', s', N')` related to `D` by an étale map `E : 𝒟' ⟶ 𝒟` over `𝔸¹_B` and
an étale map `ψ : N' ⟶ N` of normal cones, compatible with the sections and the fibres over
`t = 1` and `t = 0`. Then the identifications along `e` and `ψ` carry `α_{g',s'}` to
`α_{g,s}`. -/
theorem sectionInvariantEtaleIso_trans_sectionInvariantIso (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] {V V' B : Scheme.{u}} {d : ℕ}
    {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)
    [HasInvertibleExponent Λ B] [HasCompactification g] [HasCompactification N.proj]
    {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [QuasiCompact D.proj] {g' : V' ⟶ B} {s' : B ⟶ V'} {N' : NormalConeData d s'}
    (D' : DeformationToNormalConeData d g' s' N') [HasCompactification g']
    [HasCompactification N'.proj] [QuasiCompact D'.proj]
    (e : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e]
    (hg : e ≫ g = g') (hs : s' ≫ e = s)
    (ψ : N'.scheme ⟶ N.scheme) [_root_.AlgebraicGeometry.Etale ψ] [HasCompactification ψ]
    (hπ : ψ ≫ N.proj = N'.proj) (hz : N'.zeroSection ≫ ψ = N.zeroSection)
    (E : D'.scheme ⟶ D.scheme) [_root_.AlgebraicGeometry.Etale E] [HasCompactification E]
    (hE : E ≫ D.proj = D'.proj) (hsect : D'.sect ≫ E = D.sect)
    (h₁ : D'.oneFibre ≫ E = e ≫ D.oneFibre) (h₀ : D'.zeroFibre ≫ E = ψ ≫ D.zeroFibre)
    [QuasiCompact g'] [QuasiCompact N'.proj] :
    sectionInvariantEtaleIso Λ e g g' hg s s' hs ≪≫ D.sectionInvariantIso Λ aB =
      D'.sectionInvariantIso Λ aB ≪≫
        sectionInvariantEtaleIso Λ ψ N.proj N'.proj hπ N.zeroSection N'.zeroSection hz := by
  have := quasiSeparatedSpace_of_quasiSeparated aB
  have : QuasiCompact g := MorphismProperty.of_isPullback D.isPullback_oneFibre inferInstance
  have : QuasiCompact N.proj := MorphismProperty.of_isPullback D.isPullback_zeroFibre inferInstance
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_oneFibre
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_zeroFibre
  have := D'.isIso_dualizingComplexBaseChangeMap Λ D'.isPullback_oneFibre
  have := D'.isIso_dualizingComplexBaseChangeMap Λ D'.isPullback_zeroFibre
  -- the étale identifications commute with restriction to `t = 1` and `t = 0`
  have c₁ := sectionInvariantEtaleIso_baseChange_hom Λ E D.proj D'.proj hE
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) e g g' hg D.oneFibre D'.oneFibre
    D.isPullback_oneFibre D'.isPullback_oneFibre h₁ D.sect D'.sect hsect s s' hs
    D.comp_oneFibre D'.comp_oneFibre
  have c₀ := sectionInvariantEtaleIso_baseChange_hom Λ E D.proj D'.proj hE
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) ψ N.proj N'.proj hπ D.zeroFibre D'.zeroFibre
    D.isPullback_zeroFibre D'.isPullback_zeroFibre h₀ D.sect D'.sect hsect
    N.zeroSection N'.zeroSection hz D.comp_zeroFibre D'.comp_zeroFibre
  let ηE := sectionInvariantEtaleIso Λ E D.proj D'.proj hE D.sect D'.sect hsect
  let ηe := sectionInvariantEtaleIso Λ e g g' hg s s' hs
  let κ := D.familyObjectIso Λ aB (D.oneFibreIso Λ)
  -- the comparison of `D` transported along the étale identifications is the one of `D'`
  have hκ : ηE ≪≫ κ ≪≫ (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).mapIso ηe.symm =
      D'.familyObjectIso Λ aB (D'.oneFibreIso Λ) := by
    refine D'.eq_familyObjectIso Λ aB _ _ ?_
    have n := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).hom.naturality ηe.inv
    simp only [Functor.comp_map, Functor.id_map] at n
    have hn := D.leftDerivedUpperStar_map_familyObjectIso_hom_comp Λ aB (D.oneFibreIso Λ)
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
      Category.assoc, n]
    rw [reassoc_of% hn, oneFibreIso, oneFibreIso, ← cancel_epi
      (sectionInvariantBaseChangeIso Λ D'.isPullback_oneFibre D'.sect s'
        D'.comp_oneFibre).inv, reassoc_of% c₁]
    simp [ηe]
  have k₀ : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map
        ηE.inv ≫ (sectionInvariantBaseChangeIso Λ D'.isPullback_zeroFibre D'.sect N'.zeroSection
          D'.comp_zeroFibre).hom ≫
        (sectionInvariantEtaleIso Λ ψ N.proj N'.proj hπ N.zeroSection N'.zeroSection hz).hom =
      (sectionInvariantBaseChangeIso Λ D.isPullback_zeroFibre D.sect N.zeroSection
        D.comp_zeroFibre).hom := by
    rw [← c₀, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have n := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B)).inv.naturality ηe.hom
  simp only [Functor.comp_map, Functor.id_map] at n
  ext
  simp only [sectionInvariantIso, sectionInvariantIsoOfFibreIso, ← hκ, zeroFibreIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv,
    Functor.map_comp, Category.assoc, k₀]
  rw [reassoc_of% n]

end Scheme.Hom.DeformationToNormalConeData

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
  have : HasCompactification (Hom.normalConeData d hs).proj :=
    inferInstanceAs (HasCompactification (Hom.normalConeProj g s))
  have : HasCompactification
      (Hom.normalConeData d (comp_comp_eq_id_of_isPullback g s e s' he hs)).proj :=
    inferInstanceAs (HasCompactification (Hom.normalConeProj (e ≫ g) s'))
  have : QuasiCompact (Hom.deformationToNormalConeData d g s hs).proj :=
    inferInstanceAs (QuasiCompact (Hom.deformationSpaceProj g s))
  have : QuasiCompact
      (Hom.deformationToNormalConeData d (e ≫ g) s'
        (comp_comp_eq_id_of_isPullback g s e s' he hs)).proj :=
    inferInstanceAs (QuasiCompact (Hom.deformationSpaceProj (e ≫ g) s'))
  have : QuasiCompact (Hom.normalConeData d
      (comp_comp_eq_id_of_isPullback g s e s' he hs)).proj :=
    inferInstanceAs (QuasiCompact (Hom.normalConeProj (e ≫ g) s'))
  let D := Hom.deformationToNormalConeData d g s hs
  let D' := Hom.deformationToNormalConeData d (e ≫ g) s'
    (comp_comp_eq_id_of_isPullback g s e s' he hs)
  let E : D'.scheme ⟶ D.scheme := IdealSheafData.deformationSpaceMap e s.ker s'.ker
    (Hom.map_siteIdeal_ker_le_of_isPullback s e s' he)
  let ψ : (Hom.normalConeData d (comp_comp_eq_id_of_isPullback g s e s' he hs)).scheme ⟶
      (Hom.normalConeData d hs).scheme :=
    IdealSheafData.normalConeMap e s.ker s'.ker (Hom.map_siteIdeal_ker_le_of_isPullback s e s' he)
  have : _root_.AlgebraicGeometry.Etale E :=
    Hom.etale_deformationSpaceMap_of_isPullback s e s' he
  have : HasCompactification E :=
    HasCompactification.of_isPullback (IdealSheafData.isPullback_deformationSpaceMap_of_flat e
      s.ker s'.ker _ (Hom.ker_eq_comap_of_isPullback s e s' he)).flip
  have : IsIso ψ := Hom.isIso_normalConeMap_of_isPullback s e s' he
  have hπ : ψ ≫ (Hom.normalConeData d hs).proj =
      (Hom.normalConeData d (comp_comp_eq_id_of_isPullback g s e s' he hs)).proj :=
    Hom.normalConeMap_normalConeProj_of_isPullback s e s' he g
  have hz : (Hom.normalConeData d (comp_comp_eq_id_of_isPullback g s e s' he hs)).zeroSection ≫
      ψ = (Hom.normalConeData d hs).zeroSection :=
    Hom.normalConeZeroSection_normalConeMap_of_isPullback s e s' he
  have hE : E ≫ D.proj = D'.proj :=
    Hom.deformationSpaceMap_deformationSpaceProj_of_isPullback s e s' he g
  have hsect : D'.sect ≫ E = D.sect :=
    Hom.deformationSpaceSection_deformationSpaceMap_of_isPullback s e s' he
  have h₁ : D'.oneFibre ≫ E = e ≫ D.oneFibre :=
    Hom.deformationSpaceOneFibre_deformationSpaceMap_of_isPullback s e s' he g
  have h₀ : D'.zeroFibre ≫ E = ψ ≫ D.zeroFibre :=
    (IdealSheafData.normalConeMap_normalConeToDeformationSpace _ _ _ _).symm
  exact Hom.DeformationToNormalConeData.sectionInvariantEtaleIso_trans_sectionInvariantIso Λ D aB
    D' e rfl _ ψ hπ hz E hE hsect h₁ h₀

end Etale

end AlgebraicGeometry
