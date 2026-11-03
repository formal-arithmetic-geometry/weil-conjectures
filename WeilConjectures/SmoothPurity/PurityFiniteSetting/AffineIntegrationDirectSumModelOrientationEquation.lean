/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DualizingUnitComposite
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelSigmaOrdinaryComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.AffineIntegrationOrdinaryDirectSum

/-! # Direct-sum integration in model-orientation coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] compatibleTensor

private theorem pull_comparison_iso_naturality (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : Etale.DerivedCategoryModule P.Coefficient Y} (a : K ≅ L) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.mapIso a) ≪≫
      Dnc.pullComparison P f L =
    Dnc.pullComparison P f K ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso a) := by
  let e :=
    Functor.isoWhiskerLeft
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f) ≪≫
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) f ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).symm
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  apply Iso.ext
  exact e.hom.naturality a.hom

private theorem tensor_comparison_iso_naturality (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) {K K' L L' : Etale.DerivedCategoryModule P.Coefficient X}
    (a : K ≅ K') (b : L ≅ L') :
    P.compatibleTensorIso
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso a)
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso b) ≪≫
      (compatibleComparisonTensor P.Coefficient X K' L').symm =
    (compatibleComparisonTensor P.Coefficient X K L).symm ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (compatibleBifunctorIso
          (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X) a b) := by
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  have h := compatibleTensorComparison_naturality
    (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X)
    (ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X)
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    (ProEtale.comparisonTensorNatIso P.Coefficient X) a b
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj] at h
  have hm₁ := congrArg (fun n ↦ n.app L')
    (ProEtale.comparison_tensor_app P.Coefficient X K')
  have hm₂ := congrArg (fun n ↦ n.app L)
    (ProEtale.comparison_tensor_app P.Coefficient X K)
  rw [hm₁, hm₂] at h
  exact (compatibleIso_inverse_square _ _ _ _ h).symm

private theorem orientation_comparison (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (r : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension r f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := Dnc.compactifiable P f aY
    P.modelOrientation r f aY = P.affineIntegrationUnitComparison f ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (P.chartOrdinaryOrientation r f aY) := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := Dnc.compactifiable P f aY
  unfold modelOrientation affineIntegrationUnitComparison
  rw [(P.chartOrdinaryOrientation_spec r f aY).2]
  exact (Iso.trans_assoc _ _ _).symm

private theorem compared_orientation_product (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    letI := P.noetherian aZ
    letI := P.noetherian (g ≫ aZ)
    letI := P.noetherian (f ≫ g ≫ aZ)
    letI := Dnc.compactifiable P f (g ≫ aZ)
    letI := Dnc.compactifiable P g aZ
    (P.affineIntegrationTensorComparison f g).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        ((compatibleBifunctorIso (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X)
          (P.chartOrdinaryOrientation d f (g ≫ aZ))
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
            (P.chartOrdinaryOrientation e g aZ))).hom ≫
          (P.affineIntegrationOrdinaryMu d e f (g ≫ aZ)).hom) =
    (P.compatibleTensorIso (P.modelOrientation d f (g ≫ aZ))
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (P.modelOrientation e g aZ))).hom ≫ (P.modelOrientationMu d e f (g ≫ aZ)).hom := by
  let := P.noetherian aZ
  let := P.noetherian (g ≫ aZ)
  let := P.noetherian (f ≫ g ≫ aZ)
  let := Dnc.compactifiable P f (g ≫ aZ)
  let := Dnc.compactifiable P g aZ
  rw [orientation_comparison P d f (g ≫ aZ), orientation_comparison P e g aZ]
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let S := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
  let E := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
  let A := P.chartOrdinaryOrientation d f (g ≫ aZ)
  let B := P.chartOrdinaryOrientation e g aZ
  let T := Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X
  have hp := pull_comparison_iso_naturality P f B
  have ht := tensor_comparison_iso_naturality P X A (E.mapIso B)
  have hm := tensor_comparison_iso_naturality P X
    (Iso.refl (P.diagonalTwistEtale X d))
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates
      (Etale.projectiveLineTraceTransport P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level)
        P.Coefficient P.diagonalExponent_annihilates)
      f (P.diagonalExponent_isUnit (g ≫ aZ)) e)
  let t := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates
    (Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates)
    f (P.diagonalExponent_isUnit (g ≫ aZ)) e
  let μ := (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates X d e).symm
  have hpath :
      P.compatibleTensorIso
          (P.affineIntegrationUnitComparison f ≪≫ C.mapIso A)
          (S.mapIso (P.affineIntegrationUnitComparison g ≪≫
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.mapIso B)) ≪≫
        P.compatibleTensorIso (Iso.refl _)
          (Dnc.pullComparison P f (P.diagonalTwistEtale Y e) ≪≫ C.mapIso t) =
      P.compatibleTensorIso (P.affineIntegrationUnitComparison f)
          (S.mapIso (P.affineIntegrationUnitComparison g) ≪≫
            Dnc.pullComparison P f (P.diagonalOrdinaryDualizing g)) ≪≫
        P.compatibleTensorIso (C.mapIso A) (C.mapIso (E.mapIso B)) ≪≫
          P.compatibleTensorIso (Iso.refl _) (C.mapIso t) := by
    simp only [compatibleTensorIso, Functor.mapIso_trans,
      compatibleBifunctorIso_trans, Iso.trans_refl, Iso.trans_assoc]
    rw [← Iso.trans_assoc (S.mapIso
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.mapIso B))
      (Dnc.pullComparison P f (P.diagonalTwistEtale Y e)) (C.mapIso t), hp]
    simp only [Iso.trans_assoc]
    rfl
  simp only [Functor.mapIso_trans] at hpath
  simp only [Functor.mapIso_refl] at hm
  have hmove := congrArg
    (fun i ↦ i ≪≫ C.mapIso (compatibleBifunctorIso T (Iso.refl _) t)) ht
  simp only [Iso.trans_assoc] at hmove
  erw [← hm] at hmove
  have hi :
      P.affineIntegrationTensorComparison f g ≪≫
        C.mapIso (compatibleBifunctorIso T A (E.mapIso B) ≪≫
          P.affineIntegrationOrdinaryMu d e f (g ≫ aZ)) =
      P.compatibleTensorIso
          (P.affineIntegrationUnitComparison f ≪≫ C.mapIso A)
          (S.mapIso (P.affineIntegrationUnitComparison g ≪≫
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.mapIso B)) ≪≫
        P.modelOrientationMu d e f (g ≫ aZ) := by
    unfold affineIntegrationTensorComparison affineIntegrationOrdinaryMu
      modelOrientationMu modelOrientationTwistPullback modelOrientationPowerMul
    simp only [Functor.mapIso_trans]
    change _ = _ ≪≫ (P.compatibleTensorIso (Iso.refl _)
      (Dnc.pullComparison P f (P.diagonalTwistEtale Y e) ≪≫ C.mapIso t) ≪≫
        (compatibleComparisonTensor P.Coefficient X
          (P.diagonalTwistEtale X d) (P.diagonalTwistEtale X e)).symm ≪≫ C.mapIso μ)
    conv_rhs => rw [← Iso.trans_assoc, hpath]
    simp only [Iso.trans_assoc]
    simpa only [C, S, E, T, t, μ, diagonalTwistEtale, Iso.trans_assoc] using congrArg
      (fun i ↦ P.compatibleTensorIso (P.affineIntegrationUnitComparison f)
        (S.mapIso (P.affineIntegrationUnitComparison g) ≪≫
          Dnc.pullComparison P f (P.diagonalOrdinaryDualizing g)) ≪≫ i ≪≫ C.mapIso μ)
      hmove.symm
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp] using congrArg Iso.hom hi

/-- The coefficient-unit direct-sum equation before canonical affine transport.
Source: latest blueprint, composition proof Step 1.
(blueprint: new-pur-affine-integration-direct-sum-model-orientation-equation).

Proof: factor the three model orientations through their ordinary origins using
chartOrdinaryOrientation_spec. The orientation-free sigma site-comparison equation
rewrites the left side as comparison of the ordinary composition map. Apply the
ordinary direct-sum orientation equation under the comparison functor. Naturality
of the pullback comparison and of the monoidal site comparison, together with
bifunctor composition, rewrites the resulting ordinary tensor product as the two
model orientations followed by modelOrientationMu. This assembly is proved below;
the geometric ordinary direct-sum equation and the orientation-free site equation
are the two separate inputs.
-/
theorem affine_integration_directSum_model_orientation_equation
    (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
    letI := DiagonalPasting.affineDimension e B
    letI := DiagonalPasting.affineDimension (d + e) B
    letI : SmoothOfRelativeDimension (d + e)
        (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) :=
      smoothOfRelativeDimension_comp (n := d) (m := e)
        (DiagonalPasting.q d e B) (DiagonalPasting.pr e B)
    letI := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
    letI := Dnc.compactifiable P (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)
    ProEtale.CompositionTensorMate.sigma P.Coefficient
        (DiagonalPasting.q d e B) (DiagonalPasting.pr e B) ≫
      (P.modelOrientation (d + e)
        (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB).hom =
      (P.compatibleTensorIso
        (P.modelOrientation d (DiagonalPasting.q d e B)
          (DiagonalPasting.pr e B ≫ aB))
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (DiagonalPasting.q d e B)).leftDerivedFunctor.mapIso
          (P.modelOrientation e (DiagonalPasting.pr e B) aB))).hom ≫
      (P.modelOrientationMu d e (DiagonalPasting.q d e B)
        (DiagonalPasting.pr e B ≫ aB)).hom := by
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  let := DiagonalPasting.affineDimension e B
  let := DiagonalPasting.affineDimension (d + e) B
  let : SmoothOfRelativeDimension (d + e)
      (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) :=
    smoothOfRelativeDimension_comp (n := d) (m := e)
      (DiagonalPasting.q d e B) (DiagonalPasting.pr e B)
  let := P.noetherian aB
  let := P.noetherian (DiagonalPasting.pr e B ≫ aB)
  let := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
  let := Dnc.compactifiable P (DiagonalPasting.q d e B)
    (DiagonalPasting.pr e B ≫ aB)
  let := Dnc.compactifiable P (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB
  rw [orientation_comparison P (d + e)
    (DiagonalPasting.q d e B ≫ DiagonalPasting.pr e B) aB]
  simp only [Iso.trans_hom, ← Category.assoc]
  rw [affineIntegration_sigma_site_comparison P d e
    (DiagonalPasting.q d e B) (DiagonalPasting.pr e B) aB]
  simp only [Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, affineIntegration_ordinary_directSum P B d e aB]
  exact compared_orientation_product P d e
    (DiagonalPasting.q d e B) (DiagonalPasting.pr e B) aB

end WeilConjectures.PurityFiniteSetting
