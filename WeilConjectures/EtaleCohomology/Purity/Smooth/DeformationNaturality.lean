/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DeformationIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantBaseChangeCoherence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantEtale

/-!
# Naturality of the DNC isomorphism under base change and étale maps

Let `g : V ⟶ B` be smooth with a closed section `s`, and let
`α_{g,s} : 𝒞(g, s) ≅ 𝒞(π_N, 0_N)` be the comparison of section invariants given by a deformation
to the normal cone (`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.sectionInvariantIso`,
blueprint `lemma-section-normal-bundle`). Blueprint `lemma-naturality-under-base-change-etale`
states that `α` is natural:

* (1) under base change `h : B' ⟶ B`, through the base change isomorphisms of section
  invariants (`AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`):
  `Scheme.Hom.DeformationToNormalConeData.sectionInvariantIso_baseChange`;
* (2) under étale maps of pairs, through the identifications obtained by composing adjunctions
  (`AlgebraicGeometry.Etale.sectionInvariantEtaleIso`):
  `Scheme.Hom.DeformationToNormalConeData.sectionInvariantEtaleIso_sectionInvariantIso`.

Deformation data are carried as data
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`), so the geometric identifications
of the blueprint (`AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange`,
`AlgebraicGeometry.Scheme.Hom.exists_isPullback_normalCone_baseChange`) enter as maps of data
forming cartesian squares compatible with the sections and the fibres.

Both proofs follow the blueprint: the comparison over `𝔸¹_B` is unique once normalized at
`t = 1` (`DeformationToNormalConeData.eq_familyObjectIso`), the transported comparison is still
normalized at `t = 1`, and restricting to `t = 0` gives the claim.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- *Reading a base-changed family at a section.* Let `F : X ⟶ P` with a section `σ`, base changed
along `v : P' ⟶ P` to `F' : X' ⟶ P'` with section `σ'`, and let `i : B ⟶ P`, `i' : B' ⟶ P'` be
sections over `h : B' ⟶ B` with fibres `f : Y ⟶ B`, `f' : Y' ⟶ B'`, so that `f'` is the base
change of `f` along `h`. Let `θ : Li^* 𝒞(F, σ) ≅ 𝒞(f, s)` be the fibre identification and
`κ : 𝒞(F', σ') ≅ La'^* C₀` a trivialization. Reading the trivialization `β ≫ κ` of
`Lv^* 𝒞(F, σ)` at `i'` against `θ` (`AlgebraicGeometry.Etale.sectionRestrictionIso`) gives the base
change isomorphism `Lh^* 𝒞(f, s) ≅ 𝒞(f', s')`, followed by the fibre identification of `F'` at `i'`
read through `κ`. -/
theorem sectionRestrictionIso_sectionInvariantBaseChangeIso {P P' B B' X X' Y Y' : Scheme.{u}}
    {F : X ⟶ P} {F' : X' ⟶ P'} {v : P' ⟶ P} {hD : X' ⟶ X} [HasCompactification F]
    [HasCompactification F'] [QuasiCompact F] [QuasiCompact F'] (sqD : IsPullback hD F' F v)
    {h : B' ⟶ B} {i : B ⟶ P} {i' : B' ⟶ P'} (hi : i' ≫ v = h ≫ i) {a' : P' ⟶ B'}
    (hsec' : i' ≫ a' = 𝟙 B') {f : Y ⟶ B} {f' : Y' ⟶ B'} {ι : Y ⟶ X} {ι' : Y' ⟶ X'}
    {hY : Y' ⟶ Y} [HasCompactification f] [HasCompactification f'] [QuasiCompact f]
    [QuasiCompact f'] (sq₁ : IsPullback ι f F i) (sq₂ : IsPullback ι' f' F' i')
    (sqV : IsPullback hY f' f h) (hι : ι' ≫ hD = hY ≫ ι)
    [IsIso (dualizingComplexBaseChangeMap Λ sqD)] [IsIso (dualizingComplexBaseChangeMap Λ sq₁)]
    [IsIso (dualizingComplexBaseChangeMap Λ sq₂)] [IsIso (dualizingComplexBaseChangeMap Λ sqV)]
    [IsIso (dualizingComplexBaseChangeMap Λ (sq₂.paste_horiz sqD))]
    {σ : P ⟶ X} {σ' : P' ⟶ X'} (hσ : σ' ≫ hD = v ≫ σ) {s : B ⟶ Y} {s' : B' ⟶ Y'}
    (hs₁ : s ≫ ι = i ≫ σ) (hs₂ : s' ≫ ι' = i' ≫ σ') (hs : s' ≫ hY = h ≫ s)
    {C₀ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (κ : sectionInvariant Λ F' σ' ≅ (L((a')^*[ModuleCat.{u + 1} Λ])).obj C₀) :
    sectionRestrictionIso (ModuleCat.{u + 1} Λ) h v hi hsec'
        (sectionInvariantBaseChangeIso Λ sq₁ σ s hs₁)
        (sectionInvariantBaseChangeIso Λ sqD σ σ' hσ ≪≫ κ) =
      sectionInvariantBaseChangeIso Λ sqV s s' hs ≪≫
        (sectionInvariantBaseChangeIso Λ sq₂ σ' s' hs₂).symm ≪≫
        (L((i')^*[ModuleCat.{u + 1} Λ])).mapIso κ ≪≫
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) i' a' hsec').app C₀ := by
  have hs₃ : s' ≫ ι' ≫ hD = (i' ≫ v) ≫ σ := by
    rw [reassoc_of% hs₂, hσ, Category.assoc]
  have ha := sectionInvariantBaseChangeIso_paste_horiz Λ sqD sq₂ (sq₂.paste_horiz sqD) rfl rfl
    σ σ' s' hσ hs₂ hs₃
  have hb := sectionInvariantBaseChangeIso_paste_horiz Λ sq₁ sqV (sq₂.paste_horiz sqD) hi hι
    σ s s' hs₁ hs hs₃
  have ha' : (sectionInvariantBaseChangeIso Λ (sq₂.paste_horiz sqD) σ s' hs₃).hom ≫
      (sectionInvariantBaseChangeIso Λ sq₂ σ' s' hs₂).inv =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) i' v).hom.app _ ≫
        (L((i')^*[ModuleCat.{u + 1} Λ])).map
          (sectionInvariantBaseChangeIso Λ sqD σ σ' hσ).hom := by
    rw [ha]
    simp
  have hb' : (sectionInvariantBaseChangeIso Λ sqV s s' hs).hom =
      (L((h)^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantBaseChangeIso Λ sq₁ σ s hs₁).inv ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h i (i' ≫ v) hi).inv.app _ ≫
        (sectionInvariantBaseChangeIso Λ (sq₂.paste_horiz sqD) σ s' hs₃).hom := by
    rw [hb]
    simp
  ext
  simp only [sectionRestrictionIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc, hb', reassoc_of% ha']

end Etale

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
  {V B : Scheme.{u}} {d : ℕ} {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s}
  (D : DeformationToNormalConeData d g s N) [HasInvertibleExponent Λ B] [HasCompactification g]
  [HasCompactification N.proj] {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
  [LocallyOfFiniteType aB] [QuasiCompact D.proj]

/-- Blueprint `lemma-naturality-under-base-change-etale` (3): *naturality under base change.*
Let `h : B' ⟶ B` and let `D'` be a deformation datum for the base change `(g', s', N')`, related
to `D` by cartesian squares `hV : V' ⟶ V` over `h` (so `V' = V ×_B B'`), `hN : N' ⟶ N` over `h`
(`N_{s'} ≅ N_s ×_B B'`) and `hD : 𝒟' ⟶ 𝒟` over `𝔸¹_h` (`𝒟_{s'} V' ≅ 𝒟_s V ×_B B'`), compatible
with the sections and with the fibres over `t = 1` and `t = 0`. Then, through the exceptional base
change isomorphisms of section invariants
(`AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`), the square

`Lh^* 𝒞(g, s) ⟶ Lh^* 𝒞(π, 0)`, `𝒞(g', s') ⟶ 𝒞(π', 0')`

formed by `Lh^* α_{g,s}` and `α_{g',s'}` commutes. -/
theorem sectionInvariantIso_baseChange {V' B' : Scheme.{u}} {g' : V' ⟶ B'} {s' : B' ⟶ V'}
    {N' : NormalConeData d s'} (D' : DeformationToNormalConeData d g' s' N')
    [HasInvertibleExponent Λ B'] [HasCompactification g'] [HasCompactification N'.proj]
    {k' : Type u} [Field k'] (aB' : B' ⟶ Spec (.of k')) [IsSeparated aB']
    [LocallyOfFiniteType aB'] [QuasiCompact D'.proj] [QuasiCompact g'] [QuasiCompact N'.proj]
    (h : B' ⟶ B)
    (hV : V' ⟶ V) (sqV : IsPullback hV g' g h) (hs : s' ≫ hV = h ≫ s)
    (hN : N'.scheme ⟶ N.scheme) (sqN : IsPullback hN N'.proj N.proj h)
    (hz : N'.zeroSection ≫ hN = h ≫ N.zeroSection)
    (hD : D'.scheme ⟶ D.scheme) (sqD : IsPullback hD D'.proj D.proj (AffineSpace.map _ h))
    (hsect : D'.sect ≫ hD = AffineSpace.map _ h ≫ D.sect)
    (h₁ : D'.oneFibre ≫ hD = hV ≫ D.oneFibre) (h₀ : D'.zeroFibre ≫ hD = hN ≫ D.zeroFibre)
    [IsIso (dualizingComplexBaseChangeMap Λ sqV)] [IsIso (dualizingComplexBaseChangeMap Λ sqN)] :
    (L((h)^*[ModuleCat.{u + 1} Λ])).map (D.sectionInvariantIso Λ aB).hom ≫
        (sectionInvariantBaseChangeIso Λ sqN N.zeroSection N'.zeroSection hz).hom =
      (sectionInvariantBaseChangeIso Λ sqV s s' hs).hom ≫ (D'.sectionInvariantIso Λ aB').hom := by
  have := quasiSeparatedSpace_of_quasiSeparated aB
  have := quasiSeparatedSpace_of_quasiSeparated aB'
  have : QuasiCompact g := MorphismProperty.of_isPullback D.isPullback_oneFibre inferInstance
  have : QuasiCompact N.proj := MorphismProperty.of_isPullback D.isPullback_zeroFibre inferInstance
  have := D.isIso_dualizingComplexBaseChangeMap Λ sqD
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_oneFibre
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_zeroFibre
  have := D'.isIso_dualizingComplexBaseChangeMap Λ D'.isPullback_oneFibre
  have := D'.isIso_dualizingComplexBaseChangeMap Λ D'.isPullback_zeroFibre
  have := D.isIso_dualizingComplexBaseChangeMap Λ (D'.isPullback_oneFibre.paste_horiz sqD)
  have := D.isIso_dualizingComplexBaseChangeMap Λ (D'.isPullback_zeroFibre.paste_horiz sqD)
  -- the comparison of `D'` normalized at `t = 1`
  let κ' := D'.familyObjectIso Λ aB' (D'.oneFibreIso Λ)
  have key := D.leftDerivedUpperStar_mapIso_sectionInvariantIsoOfFibreIso Λ aB (D.oneFibreIso Λ)
    (D.zeroFibreIso Λ) h (sectionInvariantBaseChangeIso Λ sqD D.sect D'.sect hsect ≪≫ κ')
  rw [oneFibreIso, zeroFibreIso,
    sectionRestrictionIso_sectionInvariantBaseChangeIso Λ sqD (AffineSpace.oneSection_comp_map h)
      (AffineSpace.oneSection_comp_over _ B') D.isPullback_oneFibre D'.isPullback_oneFibre sqV h₁
      hsect D.comp_oneFibre D'.comp_oneFibre hs,
    sectionRestrictionIso_sectionInvariantBaseChangeIso Λ sqD (AffineSpace.zeroSection_comp_map h)
      (AffineSpace.zeroSection_comp_over _ B') D.isPullback_zeroFibre D'.isPullback_zeroFibre sqN
      h₀ hsect D.comp_zeroFibre D'.comp_zeroFibre hz] at key
  -- at `t = 1` the comparison `κ'` reads as the fibre identification of `D'`
  have e₁ : (D'.oneFibreIso Λ).symm ≪≫
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B')^*[ModuleCat.{u + 1} Λ])).mapIso κ' ≪≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B')).app _ = Iso.refl _ := by
    ext
    simp [κ', D'.leftDerivedUpperStar_map_familyObjectIso_hom_comp Λ aB' (D'.oneFibreIso Λ)]
  -- at `t = 0` it reads as the DNC isomorphism of `D'`
  have e₀ : (D'.zeroFibreIso Λ).symm ≪≫
      (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B')^*[ModuleCat.{u + 1} Λ])).mapIso κ' ≪≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) _ _
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B')).app _ =
      (D'.sectionInvariantIso Λ aB').symm := by
    ext
    simp [κ', sectionInvariantIso, sectionInvariantIsoOfFibreIso]
  rw [← oneFibreIso, ← zeroFibreIso, ← oneFibreIso, ← zeroFibreIso, e₁, e₀] at key
  have k := congrArg Iso.hom key
  simp only [sectionInvariantIso, Functor.mapIso_hom, Iso.trans_hom, Iso.refl_hom,
    Category.comp_id, Iso.symm_hom] at k
  simp [sectionInvariantIso, k]

/-- Blueprint `lemma-naturality-under-base-change-etale` (7): *naturality under étale maps of
pairs.* Let `e : V' ⟶ V` be an étale `B`-morphism with `g' = e ≫ g` and `s' ≫ e = s`, and let
`D'` be a deformation datum for `(g', s', N')` related to `D` by an étale map `E : 𝒟' ⟶ 𝒟` over
`𝔸¹_B` and an étale map `ψ : N' ⟶ N` of normal cones (an isomorphism, blueprint (4)), compatible
with the sections and the fibres over `t = 1` and `t = 0`. Then the identifications
`𝒞(g', s') ≅ 𝒞(g, s)` and `𝒞(π', 0') ≅ 𝒞(π, 0)` obtained by composing adjunctions
(`AlgebraicGeometry.Etale.sectionInvariantEtaleIso`) carry `α_{g',s'}` to `α_{g,s}`. -/
theorem sectionInvariantEtaleIso_sectionInvariantIso [QuasiCompact g] [QuasiCompact N.proj]
    {V' : Scheme.{u}} {g' : V' ⟶ B} {s' : B ⟶ V'} {N' : NormalConeData d s'}
    (D' : DeformationToNormalConeData d g' s' N') [HasCompactification g']
    [HasCompactification N'.proj] [QuasiCompact D'.proj] [QuasiCompact g'] [QuasiCompact N'.proj]
    (e : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e]
    (hg : e ≫ g = g') (hs : s' ≫ e = s)
    (ψ : N'.scheme ⟶ N.scheme) [_root_.AlgebraicGeometry.Etale ψ] [HasCompactification ψ]
    (hπ : ψ ≫ N.proj = N'.proj) (hz : N'.zeroSection ≫ ψ = N.zeroSection)
    (E : D'.scheme ⟶ D.scheme) [_root_.AlgebraicGeometry.Etale E] [HasCompactification E]
    (hE : E ≫ D.proj = D'.proj) (hsect : D'.sect ≫ E = D.sect)
    (h₁ : D'.oneFibre ≫ E = e ≫ D.oneFibre) (h₀ : D'.zeroFibre ≫ E = ψ ≫ D.zeroFibre) :
    (sectionInvariantEtaleIso Λ e g g' hg s s' hs).hom ≫ (D.sectionInvariantIso Λ aB).hom =
      (D'.sectionInvariantIso Λ aB).hom ≫
        (sectionInvariantEtaleIso Λ ψ N.proj N'.proj hπ N.zeroSection N'.zeroSection hz).hom := by
  have := quasiSeparatedSpace_of_quasiSeparated aB
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_oneFibre
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_zeroFibre
  have := D'.isIso_dualizingComplexBaseChangeMap Λ D'.isPullback_oneFibre
  have := D'.isIso_dualizingComplexBaseChangeMap Λ D'.isPullback_zeroFibre
  -- the étale identifications commute with restriction to `t = 1` and `t = 0`
  have c₁ := sectionInvariantEtaleIso_baseChange Λ E D.proj D'.proj hE
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) g g' D.oneFibre D'.oneFibre
    D.isPullback_oneFibre D'.isPullback_oneFibre e hg h₁.symm D.sect D'.sect hsect s s' hs
    D.comp_oneFibre D'.comp_oneFibre
  have c₀ := sectionInvariantEtaleIso_baseChange Λ E D.proj D'.proj hE
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) N.proj N'.proj D.zeroFibre D'.zeroFibre
    D.isPullback_zeroFibre D'.isPullback_zeroFibre ψ hπ h₀.symm D.sect D'.sect hsect
    N.zeroSection N'.zeroSection hz D.comp_zeroFibre D'.comp_zeroFibre
  change _ = _ ≫ (sectionInvariantEtaleIso Λ ψ N.proj N'.proj hπ N.zeroSection N'.zeroSection
    hz).hom at c₀
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
    rw [reassoc_of% hn]
    change (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map ηE.hom ≫
      (sectionInvariantBaseChangeIso Λ D.isPullback_oneFibre D.sect s D.comp_oneFibre).hom ≫
        ηe.inv = _
    rw [reassoc_of% c₁]
    simp [oneFibreIso, ηe]
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
  simp only [sectionInvariantIso, sectionInvariantIsoOfFibreIso, ← hκ, zeroFibreIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv, Functor.map_comp,
    Category.assoc, k₀]
  rw [reassoc_of% n]

end Scheme.Hom.DeformationToNormalConeData

end AlgebraicGeometry
