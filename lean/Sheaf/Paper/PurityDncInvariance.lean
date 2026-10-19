/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.PurityDncComparisons
public import Sheaf.Paper.PurityDncFamily
public import Sheaf.Paper.PurityNormalCone
import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
import WeilConjectures.EtaleCohomology.TateTwist.Normalized

/-! # Deformation invariance of the section dualizing object

Source: blueprint sec-smooth-purity/sk-thm-dnc/thm-pur-dnc-invariance.md
(blueprint: thm-pur-dnc-invariance).

The normal cone and DNC are the actual extended-Rees constructions. Normalization
is expressed by reading a family trivialization at 1 and 0 through the canonical
adjunction-mate fibre maps. Quantifying this equation over every finite-type base
change expresses both coordinate normalization and arbitrary base-change compatibility.
The ordinary-etale presentation in this equation is transported by the explicit ν*
comparison; the isomorphism itself is between the actual pro-etale section objects.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.Dnc

/-- Canonical commutation of finite pro-etale pullback with ν*, derived from the
ordinary inverse-image comparison and the exact-functor derivation comparisons.
Source: Bhatt--Scholze comparison; blueprint derived pullback
(blueprint: thm-pur-dnc-invariance). -/
noncomputable def pullComparison (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}}
    (b : B' ⟶ B)
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) b).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj K) ≪≫
    (ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) b).app K ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) b).app K).symm

/-- The canonical comparison of the finite source object with its ν* presentation.
Source: blueprint finite section invariant
(blueprint: thm-pur-dnc-invariance). -/
noncomputable def sourceComparison (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) :
    sourceSection P d g aB s ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
          (sourceEtale P d g aB s) :=
  letI := SmoothOfRelativeDimension.smooth d g
  letI := compactifiable P g aB
  sectionComparison P g aB s

/-- The canonical comparison for the actual normal-bundle zero section.
Source: blueprint finite normal section invariant
(blueprint: thm-pur-dnc-invariance). -/
noncomputable def normalComparison (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    normalSection P d g aB s hs ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
          (normalEtale P d g aB s hs) :=
  letI := normalCompactifiable P d g aB s hs
  sectionComparison P (Scheme.Hom.normalConeProj g s) aB s.normalConeZeroSection

/-- There is a unique coordinate-normalized isomorphism from the section invariant
of a smooth separated finite-type map to that of its normal-bundle zero section.
The equation reads a restricted DNC family trivialization at 1 and 0. It is required
for every k-morphism from a separated finite-type B', including identity, etale, and
nonflat base changes, and for every trivialization of the restricted family pulled
back from B'. In standard coordinates the two readings are the same standard object,
so this equation says that the comparison is its identity. Conversely local standard
coordinates supply such trivializations on a covering, so this is precisely the stated
normalization and naturality, with no auxiliary comparison choices as hypotheses.
Source: blueprint sec-smooth-purity/sk-thm-dnc
(blueprint: thm-pur-dnc-invariance).
Proof:
1. Finite type over k makes B and V Noetherian. The centre (I,t), its blowup, the
   quasi-compact DNC open, and the normal vector bundle stay separated and finite
   type; arbitrary finite-type base changes remain in this domain. The geometry
   lemma identifies the two fibres and the punctured family by canonical mates.
2. The family-constancy proposition gives the unique κ:F≅a*C(g,s), normalized by
   the canonical fibre map at 1. Restrict κ inverse to 0 and compose with the canonical
   fibre map there; use i0*a*=id. This defines the required isomorphism.
3. Etale coordinates near the section give x_i=t*u_i on the DNC. Through open and
   etale exceptional-pullback comparisons this is the standard affine-space family.
   Its readings at 1 and 0 agree, giving the identity normalization. The same argument
   applies after restricting to every trivialization pulled back from any B'.
4. Cancel the common twist and shift in local coordinates. The objects are then
   sheaves of free rank one in degree zero. Fully faithful embedding of these sheaves
   in the derived category and sheaf descent make two normalized morphisms equal.
   This uses faithfulness only on the relevant sheaf Hom, not arbitrary derived Hom.
5. Extended Rees base change and the canonical adjunction-mate fibre comparisons
   commute with arbitrary base change in B. The unique κ normalized at 1 therefore
   restricts to the corresponding κ'. Restriction at 0 gives precisely the displayed
   equation, hence etale localization and nonflat base-change compatibility. -/
theorem existsUnique_dncInvariance (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    ∃! α : sourceSection P d g aB s ≅ normalSection P d g aB s hs,
      ∀ (B' : Scheme.{u}) (aB' : B' ⟶ Spec (.of P.field.k))
        [IsSeparated aB'] [LocallyOfFiniteType aB'] [QuasiCompact aB']
        (b : B' ⟶ B) (_hb : b ≫ aB = aB')
        (C₀ : _root_.DerivedCategory
          (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (e : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
            (familyEtale P d g aB s hs) ≅
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B')).leftDerivedFunctor.obj C₀),
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso α =
          (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
              (sourceComparison P d g aB s) ≪≫
            pullComparison P b (sourceEtale P d g aB s) ≪≫
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
              (Etale.sectionRestrictionIso _ b _ (AffineSpace.oneSection_comp_map b)
                  (AffineSpace.oneSection_comp_over _ B') (fibreOne P d g aB s hs) e ≪≫
                (Etale.sectionRestrictionIso _ b _ (AffineSpace.zeroSection_comp_map b)
                  (AffineSpace.zeroSection_comp_over _ B') (fibreZero P d g aB s hs) e).symm) ≪≫
            ((ProEtale.upperStar
                (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
                (normalComparison P d g aB s hs) ≪≫
              pullComparison P b (normalEtale P d g aB s hs)).symm := by
  classical
  have := noetherian P aB
  have := SmoothOfRelativeDimension.smooth d g
  have := compactifiable P g aB
  have := normalCompactifiable P d g aB s hs
  have := invertibleExponent P aB
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have hm : ((Scheme.Hom.puncturedLine B).ι ≫ s.deformationSpaceSection) ≫
      Scheme.Hom.deformationSpaceProj g s = 𝟙 _ ≫ (Scheme.Hom.puncturedLine B).ι := by
    rw [Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs,
      Category.comp_id, Category.id_comp]
  let sq := Scheme.Hom.isPullback_deformationSpaceGeneric g s
  let D : Scheme.Hom.DeformationToNormalConeData d g s (Scheme.Hom.normalConeData d hs) :=
    { scheme := s.ker.deformationSpace
      proj := Scheme.Hom.deformationSpaceProj g s
      sect := s.deformationSpaceSection
      sect_comp_proj := Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs
      smoothOfRelativeDimension_proj := inferInstance
      isSeparated_proj := inferInstance
      hasCompactification_proj :=
        Scheme.Hom.hasCompactification_deformationSpaceProj g s d hs
      oneFibre := Scheme.Hom.deformationSpaceOneFibre g s
      isPullback_oneFibre := Scheme.Hom.isPullback_deformationSpaceOneFibre g s
      comp_oneFibre := Scheme.Hom.comp_deformationSpaceOneFibre hs
      zeroFibre := s.ker.normalConeToDeformationSpace
      isPullback_zeroFibre := Scheme.Hom.isPullback_normalConeToDeformationSpace g s
      comp_zeroFibre := Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace
      puncturedLine := Scheme.Hom.puncturedLine B
      coe_puncturedLine := Scheme.Hom.coe_puncturedLine B
      generic := Scheme.Hom.deformationSpaceGeneric g s
      isPullback_generic := sq
      exists_sect_generic := ⟨sq.lift _ _ hm, by
        rw [← Scheme.Hom.deformationSpaceGeneric_toBase g s, sq.lift_fst_assoc,
          Category.assoc, Scheme.Hom.deformationSpaceSection_toBase, Category.assoc],
        sq.lift_snd _ _ _, sq.lift_fst _ _ _⟩
      exists_etale_coordinates :=
        Scheme.Hom.exists_etale_coordinates_deformationSpace d g s hs }
  have : NeZero (ringChar P.Coefficient) :=
    ⟨CharP.ringChar_ne_zero_of_finite P.Coefficient⟩
  have : HasCompactification (Scheme.Hom.normalConeData d hs).proj :=
    normalCompactifiable P d g aB s hs
  obtain ⟨ψ, hψ⟩ := Etale.exists_iso_sectionInvariant_normalCone P.Coefficient d g s
    (Scheme.Hom.normalConeData d hs) D aB (fibreOne P d g aB s hs)
      (fibreZero P d g aB s hs)
  change sourceEtale P d g aB s ≅ normalEtale P d g aB s hs at ψ
  let α := sourceComparison P d g aB s ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      ψ ≪≫ (normalComparison P d g aB s hs).symm
  apply existsUnique_of_exists_of_unique
  · refine ⟨α, ?_⟩
    intro B' aB' _ _ _ b hb C₀ e
    have he := hψ b e
    let ν := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
    let ν' := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory
    let Lb := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor
    let η : ν ⋙ Lb ≅
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor ⋙ ν' :=
      Functor.isoWhiskerLeft ν (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ b) ≪≫
        ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso _ b ≪≫
          Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ b).symm ν'
    have hn := η.hom.naturality ψ.hom
    change Lb.map (ν.map ψ.hom) ≫ (pullComparison P b _).hom =
      (pullComparison P b _).hom ≫
        ν'.map ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map
          ψ.hom) at hn
    rw [← he]
    apply Iso.ext
    simp only [α, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Iso.trans_inv, Functor.mapIso_inv]
    erw [← reassoc_of% hn]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  · intro α' α'' hα' hα''
    obtain ⟨κ⟩ := D.nonempty_iso_familyObject_leftDerivedUpperStar P.Coefficient aB
    have e : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.map (ULift.{u} (Fin 1)) (𝟙 B))).leftDerivedFunctor.obj
          (familyEtale P d g aB s hs) ≅
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj
            (sourceEtale P d g aB s) := by
      rw [AffineSpace.map_id]
      exact (Etale.leftDerivedUpperStarId _
        (AffineSpace (ULift.{u} (Fin 1)) B)).app _ ≪≫ κ
    have h := (hα' B aB (𝟙 B) (Category.id_comp aB) _ e).trans
      (hα'' B aB (𝟙 B) (Category.id_comp aB) _ e).symm
    apply Iso.ext
    have hhom := congrArg Iso.hom h
    have hn := (ProEtale.leftDerivedUpperStarId
      (ModuleCat.{u + 1} P.Coefficient) B).hom.naturality α'.hom
    have hn' := (ProEtale.leftDerivedUpperStarId
      (ModuleCat.{u + 1} P.Coefficient) B).hom.naturality α''.hom
    dsimp at hn hn' hhom
    rw [hhom] at hn
    exact (cancel_epi ((ProEtale.leftDerivedUpperStarId
      (ModuleCat.{u + 1} P.Coefficient) B).hom.app
        (sourceSection P d g aB s))).mp (hn.symm.trans hn')

end WeilConjectures.PurityFiniteSetting.Dnc
