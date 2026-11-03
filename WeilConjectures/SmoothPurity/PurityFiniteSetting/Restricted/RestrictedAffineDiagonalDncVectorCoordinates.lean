/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.RestrictedAffineDiagonalSectionTrace
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Restricted.RestrictedAffineSourceVectorCoordinates
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorSectionReesReadings
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionConstantTrivialization

/-! # Vector coordinates for the restricted diagonal DNC

Source: smooth-purity, Agreement on the model.
(blueprint: lem-pur-restricted-affine-diagonal-dnc-vector-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The actual smooth section exchange to a vector-bundle presentation over the
identity of the base, including the identity-pullback comparison.
Source: smooth-purity, section geometry (1)
(blueprint: lem-pur-restricted-affine-diagonal-dnc-vector-coordinates). -/
def vectorModelSectionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {T B : Scheme.{u}} [IsNoetherian B] (d : ℕ) (g : T ⟶ B)
    [HasCompactification g] [SmoothOfRelativeDimension d g]
    [HasInvertibleExponent A T] (s : B ⟶ T)
    (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    [QuasiCompact (VectorBundleZeroSection.π B d F)]
    (e : VectorBundleZeroSection.scheme B d F ≅ T)
    (w : e.hom ≫ g = VectorBundleZeroSection.π B d F)
    (hz : VectorBundleZeroSection.zero B d F ≫ e.hom = s) :
    Etale.sectionInvariant A g s ≅
      Etale.sectionInvariant A (VectorBundleZeroSection.π B d F)
        (VectorBundleZeroSection.zero B d F) :=
  (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).symm.app _ ≪≫
    Dnc.sectionBaseChange A d g
      (IsPullback.of_horiz_isIso ⟨w.trans (Category.comp_id _).symm⟩)
      s (VectorBundleZeroSection.zero B d F) (hz.trans (Category.id_comp _).symm)

private theorem sourceEtaleColimits (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (J : Type v) [Category.{w} J]
    [HasColimitsOfShape J (ModuleCat.{u + 1} P.Coefficient)] :
    HasColimitsOfShape J (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  Sheaf.instHasColimitsOfShape

private theorem sourceProEtaleColimits (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (J : Type v) [Category.{w} J]
    [HasColimitsOfShape J (ModuleCat.{u + 1} P.Coefficient)] :
    HasColimitsOfShape J
      (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)) :=
  Sheaf.instHasColimitsOfShape

section ProofHelpers

-- `import all` exposes this proved helper under its private numerical name.
-- Construct that name as in the library's other private proof imports.
local macro "nativeDncReading" : term =>
  pure <| Lean.mkIdent <|
    (Lean.Name.num (`_private.WeilConjectures.SmoothPurity.PurityFiniteSetting ++
      `SectionRestriction.PuritySectionConstantTrivialization) 0) ++
      `WeilConjectures.PurityFiniteSetting.SectionRestriction.delta_etale_reading

-- Cache the canonical sheaf colimit instances used by the derived functors.
attribute [local instance] sourceEtaleColimits sourceProEtaleColimits

private theorem reading_transport {C D : Type*} [Category C] [Category D]
    (A : C ⥤ D) (E : D ⥤ C) (ε : A ⋙ E ≅ 𝟭 C)
    {F : D} {K L : C} (κ : F ≅ A.obj K) (c : K ≅ L) :
    E.mapIso (κ ≪≫ A.mapIso c) ≪≫ ε.app L =
      (E.mapIso κ ≪≫ ε.app K) ≪≫ c := by
  have hn : E.mapIso (A.mapIso c) ≪≫ ε.app L = ε.app K ≪≫ c := by
    apply Iso.ext
    exact ε.hom.naturality c.hom
  rw [Functor.mapIso_trans, Iso.trans_assoc, hn, Iso.trans_assoc]

private theorem dnc_from_readings (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ}
    (X : SectionRestriction.Pair B d)
    (K : Etale.DerivedCategoryModule P.Coefficient B)
    (cS : SectionRestriction.sectionEtale P aB X ≅ K)
    (cN : Dnc.normalEtale P d X.g aB X.s X.section_eq ≅ K)
    (κ : Dnc.familyEtale P d X.g aB X.s X.section_eq ≅
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor.obj K)
    (h₁ : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
        (Etale.leftDerivedUpperStarCompSectionIso _ _ _
          (AffineSpace.oneSection_comp_over _ B)).app K =
        Dnc.fibreOne P d X.g aB X.s X.section_eq ≪≫ cS)
    (h₀ : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ ≪≫
        (Etale.leftDerivedUpperStarCompSectionIso _ _ _
          (AffineSpace.zeroSection_comp_over _ B)).app K =
        Dnc.fibreZero P d X.g aB X.s X.section_eq ≪≫ cN) :
    let ν := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
    (SectionRestriction.delta P aB X).hom ≫
        (Dnc.normalComparison P d X.g aB X.s X.section_eq).hom ≫ ν.map cN.hom =
      (Dnc.sourceComparison P d X.g aB X.s).hom ≫ ν.map cS.hom := by
  let A := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace (ULift.{u} (Fin 1)) B ↘ B)).leftDerivedFunctor
  let κ' := κ ≪≫ A.mapIso cS.symm
  have h₁' : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ' ≪≫
      (Etale.leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.oneSection_comp_over _ B)).app _ =
        Dnc.fibreOne P d X.g aB X.s X.section_eq := by
    dsimp only [κ']
    rw [reading_transport, h₁]
    simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  have h₀' : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso κ' ≪≫
      (Etale.leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.zeroSection_comp_over _ B)).app _ =
        Dnc.fibreZero P d X.g aB X.s X.section_eq ≪≫ cN ≪≫ cS.symm := by
    dsimp only [κ']
    rw [reading_transport, h₀, Iso.trans_assoc]
  have hδ := nativeDncReading P aB X κ' h₁'
  rw [h₀'] at hδ
  rw [hδ]
  simp only [Iso.trans_symm, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.map_inv_hom_id, Category.comp_id]

end ProofHelpers

/-- The restricted diagonal and its normal zero section have compatible vector
coordinates for the normalized DNC map. This is a geometric assertion: no integration,
Tate transport, beta, or choice of chart orientation appears in the conclusion.
Source: smooth-purity, Agreement on the model, standard-pair paragraph and
DNC section geometry (4).
(blueprint: lem-pur-restricted-affine-diagonal-dnc-vector-coordinates).

Proof: use restrictedAffineDiagonalCoordinates and subtract its diagonal section.
The resulting difference coordinates identify the source with the free rank-d bundle,
and also provide its global affine-space frame. Transport the published standard-pair
Rees isomorphism through this presentation using the coefficientwise Rees comparison.
It is an isomorphism because that comparison is a pullback of the source isomorphism.
The free frame identifies the constant bundle family with the same affine space over
the line. Projection and augmentation give a section-preserving family isomorphism.
Define the final e and n by its pullbacks to the actual fibres at one and zero.
Their universal properties give the endpoint, projection and zero-section equations.
Use the smooth section exchange to trivialize familyEtale; pasting identifies its
readings with vectorModelSectionComparison for these two endpoint presentations.
Apply the defining family equation of delta at the identity base change.
Naturality of the site comparison and identity-pullback unit cancels the identity
pullback factors, giving the displayed equality. This argument uses the actual
Rees fibres, not an arbitrary identification of isomorphism classes. For d=0 the
free module and all polynomial generators are empty, and the same equations are
identity equations. On the empty scheme they hold by the same universal properties. -/
theorem restrictedAffineDiagonalDncVectorCoordinates (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    [SmoothOfRelativeDimension d (affineTraceProjection Y d)]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry (affineTraceProjection Y d) aY d V) :
    letI := H.separated
    letI := H.finiteType
    letI := H.quasiCompact
    letI := H.smoothDimension
    letI := H.baseFiniteType
    letI := H.baseQuasiCompact
    letI := H.sourceSeparated
    letI := H.sourceFiniteType
    letI := H.sourceQuasiCompact
    let h := affineTraceProjection Y d ∣_ V.1
    let B := (affineTraceProjection Y d ⁻¹ᵁ V.1).toScheme
    let aB := h ≫ V.1.ι ≫ aY
    letI := P.noetherian aB
    letI := SmoothOfRelativeDimension.smooth d h
    let g := pullback.fst h h
    let s := pullback.diagonal h
    letI := Dnc.compactifiable P g aB
    letI := Dnc.invertibleExponent P (g ≫ aB)
    let q := Scheme.Hom.normalConeProj g s
    letI := Dnc.normalCompactifiable P d g aB s (pullback.diagonal_fst h)
    letI : SmoothOfRelativeDimension d q :=
      (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
    letI := Dnc.invertibleExponent P (q ≫ aB)
    let ν := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
    ∃ (F : B.Modules) (hF : F.IsFiniteLocallyFreeOfRank d),
      letI := hF
      letI := (Etale.vectorIntegration_geometry B d F).1
      letI := (Etale.vectorIntegration_geometry B d F).2.1
      letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
      ∃ (n : VectorBundleZeroSection.scheme B d F ≅ s.ker.normalCone)
        (w : n.hom ≫ q = VectorBundleZeroSection.π B d F)
        (hz : VectorBundleZeroSection.zero B d F ≫ n.hom = s.normalConeZeroSection)
        (e : VectorBundleZeroSection.scheme B d F ≅ pullback h h)
        (we : e.hom ≫ g = VectorBundleZeroSection.π B d F)
        (ze : VectorBundleZeroSection.zero B d F ≫ e.hom = s),
        (OrientationRefinement.delta P (affineTraceProjection Y d) aY d V H).hom ≫
            (Dnc.normalComparison P d g aB s (pullback.diagonal_fst h)).hom ≫
            ν.map (vectorModelSectionComparison P.Coefficient d q s.normalConeZeroSection
              F n w hz).hom =
          (Dnc.sourceComparison P d g aB s).hom ≫
            ν.map (vectorModelSectionComparison P.Coefficient d g s F e we ze).hom  := by
  have := H.separated
  have := H.finiteType
  have := H.quasiCompact
  have := H.smoothDimension
  have := H.baseFiniteType
  have := H.baseQuasiCompact
  have := H.sourceSeparated
  have := H.sourceFiniteType
  have := H.sourceQuasiCompact
  let h := affineTraceProjection Y d ∣_ V.1
  let B := (affineTraceProjection Y d ⁻¹ᵁ V.1).toScheme
  let aB := h ≫ V.1.ι ≫ aY
  have := P.noetherian aB
  have := SmoothOfRelativeDimension.smooth d h
  let g := pullback.fst h h
  let s := pullback.diagonal h
  have := Dnc.compactifiable P g aB
  have := Dnc.invertibleExponent P (g ≫ aB)
  obtain ⟨F, hF, c, wc, zc, e₀, we₀, ze₀⟩ := affineTowerSection_vectorCoordinates B d g s
    (pullback.diagonal_fst h) (OrientationCounit.restrictedAffineDiagonalCoordinates Y d V.1)
    (OrientationCounit.restrictedAffineDiagonalCoordinates_over Y d V.1)
  have := hF
  have := (Etale.vectorIntegration_geometry B d F).1
  have := (Etale.vectorIntegration_geometry B d F).2.1
  have := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  obtain ⟨e, we, ze, ⟨M⟩⟩ := vectorSection_reesCoordinates d g s
    (pullback.diagonal_fst h) F c wc zc e₀ we₀ ze₀
  obtain ⟨κ, h₁, h₀⟩ :=
    vectorSection_reesReadings P d g aB s (pullback.diagonal_fst h) F e we ze M
  let q := Scheme.Hom.normalConeProj g s
  have := Dnc.normalCompactifiable P d g aB s (pullback.diagonal_fst h)
  have : SmoothOfRelativeDimension d q :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
  have := Dnc.invertibleExponent P (q ≫ aB)
  let X : SectionRestriction.Pair B d :=
    ⟨pullback h h, g, s, inferInstance, inferInstance, inferInstance, inferInstance,
      pullback.diagonal_fst h⟩
  have hd : OrientationRefinement.delta P (affineTraceProjection Y d) aY d V H =
      SectionRestriction.delta P aB X := by
    apply (Dnc.existsUnique_dncInvariance P d g aB s (pullback.diagonal_fst h)).unique
    · exact (Dnc.existsUnique_dncInvariance P d g aB s
        (pullback.diagonal_fst h)).exists.choose_spec
    · exact (Classical.choose_spec (Dnc.existsUnique_dncInvariance P d g aB s
        (pullback.diagonal_fst h))).1
  refine ⟨F, hF, M.normal, M.normal_proj, M.normal_zero, e, we, ze, ?_⟩
  rw [hd]
  exact dnc_from_readings P aB X _
    (vectorModelSectionComparison P.Coefficient d g s F e we ze)
    (vectorModelSectionComparison P.Coefficient d q s.normalConeZeroSection
      F M.normal M.normal_proj M.normal_zero) κ h₁ h₀

end WeilConjectures.PurityFiniteSetting
