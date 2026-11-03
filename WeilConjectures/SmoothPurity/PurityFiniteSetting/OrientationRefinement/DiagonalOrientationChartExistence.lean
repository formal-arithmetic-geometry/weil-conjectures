/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationMate
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.VectorZeroSectionIntegrationBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.SmoothSectionExchangeComposition
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Existence of a normalized affine diagonal chart

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, Steps 1--3.
(blueprint: lem-pur-diagonal-orientation-refinement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale (purityTwistTransport)
namespace WeilConjectures.PurityFiniteSetting.OrientationRefinement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem vector_beta_isIso (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    IsIso (vectorBetaInverse P B aB d F) := by
  let := P.noetherian aB
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B d F).2.2
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  have hi := Etale.integration_unit_adjunct_isIso P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F
  dsimp only at hi
  have := hi
  dsimp only [vectorBetaInverse]
  rw [Adjunction.homEquiv_naturality_right]
  apply IsIso.comp_isIso' (by infer_instance)
  refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
  apply IsIso.comp_isIso' (by infer_instance)
  apply IsIso.comp_isIso' hi
  infer_instance

attribute [local irreducible] vectorBetaInverse Dnc.sectionBaseChange
  Etale.vectorIntegrationBaseCoefficientPullback

private theorem vector_beta_iso_id (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    letI := P.noetherian aB
    Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates
      (purityTwistTransport P.Coefficient P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
      (𝟙 B) (P.diagonalExponent_isUnit aB) d =
        (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app _ := by
  let := P.noetherian aB
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B d F).2.2
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  let := Dnc.invertibleExponent P (VectorBundleZeroSection.π B d F ≫ aB)
  let := (VectorBundleZeroSection.finite_type_frames P.field.k B aB d F).choose_spec.2.2.2.2.2.1
  let := vector_beta_isIso P B aB d F
  have he := vector_zero_section_integration_baseChange P B B aB aB d F F
    (𝟙 B) (𝟙 _) (IsPullback.id_horiz (VectorBundleZeroSection.π B d F))
      (by rw [Category.comp_id, Category.id_comp])
  have hid := Dnc.section_baseChange_id P.Coefficient d (VectorBundleZeroSection.π B d F)
    (VectorBundleZeroSection.zero B d F)
  have hid' := congrArg Iso.hom hid
  simp only [Iso.trans_hom, Iso.refl_hom] at hid'
  have hsec := (cancel_epi ((Etale.leftDerivedUpperStarId
    (ModuleCat.{u + 1} P.Coefficient) B).inv.app _)).1
      (hid'.trans (Iso.inv_hom_id_app _ _).symm)
  rw [hsec] at he
  have hn := (Etale.leftDerivedUpperStarId
    (ModuleCat.{u + 1} P.Coefficient) B).hom.naturality (vectorBetaInverse P B aB d F)
  simp only [Functor.id_map] at hn
  apply Iso.ext
  exact (cancel_mono (vectorBetaInverse P B aB d F)).1 (he.symm.trans hn)

private theorem has_vector_model (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V) : HasVectorModel P f aY d V H := by
  let := H.separated
  let := H.finiteType
  let := H.quasiCompact
  let := H.smoothDimension
  let := H.baseFiniteType
  let := H.baseQuasiCompact
  let := H.sourceSeparated
  let := H.sourceFiniteType
  let := H.sourceQuasiCompact
  let := SmoothOfRelativeDimension.smooth d (f ∣_ V.1)
  let := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
  obtain ⟨hF, hSym, q, e, _, _, hπ, hz⟩ := SectionReesBaseChange.normal_bundle d
    (pullback.fst (f ∣_ V.1) (f ∣_ V.1)) (pullback.diagonal (f ∣_ V.1))
    (pullback.diagonal_fst (f ∣_ V.1))
  refine ⟨_, hF, (q ≪≫ e).symm, ?_, ?_⟩
  · exact (Iso.inv_comp_eq _).2 hπ.symm
  · exact ((Iso.eq_comp_inv _).2 hz).symm

attribute [local irreducible] Etale.rightDerivedLowerShriek Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
/-- Every finite type affine target open admits the geometric and normalized chart data.
The statement is strictly one local existence component of the affine refinement theorem.
(blueprint: lem-pur-diagonal-orientation-chart-existence).
The proof constructs the normal bundle from the Rees deformation, applies the normalized
zero-section integration mate, and transports it through the canonical etale comparison.
-/
theorem diagonalOrientationChart_exists (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (V : Y.affineOpens)
    (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType) :
    Nonempty (Chart P f aY d V) := by
  obtain ⟨H, _⟩ := (P.affineTargetDiagonalDnc aY aX f hf d).2 V hV
  let := H.separated
  let := H.finiteType
  let := H.quasiCompact
  let := H.smoothDimension
  let := H.baseFiniteType
  let := H.baseQuasiCompact
  let := H.sourceSeparated
  let := H.sourceFiniteType
  let := H.sourceQuasiCompact
  let B := (f ⁻¹ᵁ V.1).toScheme
  let aB := (f ∣_ V.1) ≫ V.1.ι ≫ aY
  let := P.noetherian aB
  have hmodel := has_vector_model P f aY d V H
  obtain ⟨F, hF, e, he, hz⟩ := hmodel
  let := hF
  let g := pullback.fst (f ∣_ V.1) (f ∣_ V.1)
  let s := pullback.diagonal (f ∣_ V.1)
  let q := Scheme.Hom.normalConeProj g s
  let := Dnc.normalCompactifiable P d g aB s (pullback.diagonal_fst _)
  let : SmoothOfRelativeDimension d q :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst _)).smoothOfRelativeDimension_proj
  let := Dnc.invertibleExponent P (q ≫ aB)
  let := SmoothOfRelativeDimension.smooth d q
  let : LocallyOfFiniteType q := inferInstance
  let := Dnc.normalQuasiCompact d g s (pullback.diagonal_fst _)
  let := P.noetherian (q ≫ aB)
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B d F).2.2
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  have hq : q = e.inv ≫ VectorBundleZeroSection.π B d F := by
    rw [← he, Iso.inv_hom_id_assoc]
  let : IsAffineHom q := by rw [hq]; infer_instance
  let : IsSeparated q := inferInstance
  let := vector_beta_isIso P B aB d F
  let c := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).symm.app
      (Etale.sectionInvariant P.Coefficient q s.normalConeZeroSection) ≪≫
    Dnc.sectionBaseChange P.Coefficient d q
      (b := 𝟙 B) (f' := VectorBundleZeroSection.π B d F) (a := e.hom)
      (IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id _).symm⟩)
      s.normalConeZeroSection (VectorBundleZeroSection.zero B d F)
      (hz.trans (Category.id_comp _).symm)
  let b : normalEtale P f aY d V H ≅ P.diagonalTwistEtale B d :=
    c ≪≫ (asIso (vectorBetaInverse P B aB d F)).symm
  refine ⟨⟨H, has_vector_model P f aY d V H, b, ?_⟩⟩
  dsimp only [BetaNormalized]
  intro F' hF' e' he' hz'
  let := hF'
  let := (Etale.vectorIntegration_geometry B d F').1
  let := (Etale.vectorIntegration_geometry B d F').2.1
  let := (Etale.vectorIntegration_geometry B d F').2.2
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F') aB
  let := Dnc.invertibleExponent P (VectorBundleZeroSection.π B d F ≫ aB)
  let := (VectorBundleZeroSection.finite_type_frames P.field.k B aB d F).choose_spec.2.2.2.2.2.1
  let v := e'.hom ≫ e.inv
  have hv : v ≫ VectorBundleZeroSection.π B d F =
      VectorBundleZeroSection.π B d F' := by
    dsimp only [v]
    rw [ Category.assoc, ← he, Iso.inv_hom_id_assoc, he']
  have hzv : VectorBundleZeroSection.zero B d F' ≫ v =
      VectorBundleZeroSection.zero B d F := by
    dsimp only [v]
    rw [ ← Category.assoc, hz', ← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let sqv : IsPullback v (VectorBundleZeroSection.π B d F')
      (VectorBundleZeroSection.π B d F) (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨hv.trans (Category.comp_id _).symm⟩
  let cv := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).symm.app
      (Etale.sectionInvariant P.Coefficient (VectorBundleZeroSection.π B d F)
        (VectorBundleZeroSection.zero B d F)) ≪≫
    Dnc.sectionBaseChange P.Coefficient d (VectorBundleZeroSection.π B d F) sqv
      (VectorBundleZeroSection.zero B d F) (VectorBundleZeroSection.zero B d F')
      (hzv.trans (Category.id_comp _).symm)
  have hcomp := Dnc.section_baseChange_comp_over_id P.Coefficient d q
    (VectorBundleZeroSection.π B d F) (VectorBundleZeroSection.π B d F')
    (a := e.hom) (a' := v)
    (IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id _).symm⟩) sqv
    s.normalConeZeroSection (VectorBundleZeroSection.zero B d F)
    (VectorBundleZeroSection.zero B d F') hz hzv
  have hnat := vector_zero_section_integration_baseChange P B B aB aB d F F'
    (𝟙 B) v sqv (hzv.trans (Category.id_comp _).symm)
  have ht := congrArg Iso.hom (vector_beta_iso_id P B aB d F)
  have hnat' : (Etale.ordinaryFinitePullback P.Coefficient (𝟙 B)).map
      (vectorBetaInverse P B aB d F) ≫
      (Dnc.sectionBaseChange P.Coefficient d (VectorBundleZeroSection.π B d F) sqv
        (VectorBundleZeroSection.zero B d F) (VectorBundleZeroSection.zero B d F')
        (hzv.trans (Category.id_comp _).symm)).hom =
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).hom.app _ ≫
        vectorBetaInverse P B aB d F' :=
    hnat.trans (congrArg (fun x ↦ x ≫ vectorBetaInverse P B aB d F') ht)
  have hn := (Etale.leftDerivedUpperStarId
    (ModuleCat.{u + 1} P.Coefficient) B).inv.naturality (vectorBetaInverse P B aB d F)
  simp only [Functor.id_map] at hn
  have hcv : vectorBetaInverse P B aB d F ≫ cv.hom =
      vectorBetaInverse P B aB d F' := by
    simp only [cv, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
    erw [← Category.assoc, hn, Category.assoc, hnat', ← Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
  have hev : v ≫ e.hom = e'.hom := by simp [v]
  simp only [hev] at hcomp
  have hc : (Etale.leftDerivedUpperStarId
      (ModuleCat.{u + 1} P.Coefficient) B).inv.app
      (Etale.sectionInvariant P.Coefficient q s.normalConeZeroSection) ≫
      (Dnc.sectionBaseChange P.Coefficient d q
        (IsPullback.of_horiz_isIso ⟨he'.trans (Category.comp_id _).symm⟩)
        s.normalConeZeroSection (VectorBundleZeroSection.zero B d F')
        (hz'.trans (Category.id_comp _).symm)).hom = c.hom ≫ cv.hom := by
    exact congrArg Iso.hom hcomp
  change b.inv ≫ _ = _
  have hh := congrArg (fun x ↦ b.inv ≫ x) hc
  exact hh.trans (by
    dsimp only [b, Iso.trans_inv, Iso.symm_inv, asIso_hom]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hcv)
end WeilConjectures.PurityFiniteSetting.OrientationRefinement
