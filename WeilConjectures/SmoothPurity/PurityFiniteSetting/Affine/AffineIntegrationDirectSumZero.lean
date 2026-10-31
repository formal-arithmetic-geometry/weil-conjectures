/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelAffineIntegrationOrientationNormalized
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineIntegrationZeroSectionOrdinary
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence

/-! # Zero-section direct-sum coordinate equation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem canonical_zero_presentation (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ) :
    letI := DiagonalPasting.affineDimension r B
    P.modelOrientationZero P.modelAffineCanonicalGamma B r aB =
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
        (P.chartSectionOrientation r (DiagonalPasting.pr r B) aB
          (DiagonalPasting.zero r B)
          (Etale.projectiveLineTraceTransport P.diagonalExponent
            (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
            P.diagonalExponent_annihilates)) := by
  let := P.noetherian aB
  let := P.noetherian (DiagonalPasting.pr r B ≫ aB)
  let := DiagonalPasting.affineDimension r B
  let := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
  have h := (P.chartOrdinaryOrientation_spec r (DiagonalPasting.pr r B) aB).2
  unfold modelOrientationZero modelAffineCanonicalGamma
  dsimp only [Iso.symm_symm_eq]
  rw [h]
  simp only [Iso.symm_self_id_assoc]
  unfold modelOrientationTwistPullback
  erw [← Iso.trans_assoc
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.zero r B)).leftDerivedFunctor.mapIso
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A r B)).mapDerivedCategory.mapIso
          (P.chartOrdinaryOrientation r (DiagonalPasting.pr r B) aB)))]
  erw [Dnc.pullComparison_naturality]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, ← Functor.mapIso_trans]
  simp only [chartSectionOrientation, Functor.mapIso_trans, Iso.trans_assoc]
  rfl

/-- The canonical zero-section coordinate orientation satisfies the direct-sum law.
Source: latest blueprint, composition proof Step 1 (canonical base-change coherence).
(blueprint: lem-pur-affine-integration-direct-sum-zero-helper).

Proof: express each canonical model zero orientation as the comparison functor applied to
its ordinary section orientation. The ordinary orientation specification, pullback-comparison
naturality and cancellation give this presentation. Transport the ordinary multiplication
identity using the naturality square of the strong monoidal site comparison. Cancel the
source and target comparison isomorphisms; the remaining factors are exactly compatibleNu
and modelOrientationPowerMul. This uses no choice of a trivialization and applies to zero
ranks and empty bases.
-/
theorem affine_integration_directSum_zero_helper (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    ModelZeroOrientationEquation P P.modelAffineCanonicalGamma B d e aB  := by
  let := P.noetherian aB
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := DiagonalPasting.affineDimension d B
  let := DiagonalPasting.affineDimension e B
  let := DiagonalPasting.affineDimension (d + e) B
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  have h := affine_integration_zero_section_ordinary P B d e aB
  unfold ModelZeroOrientationEquation
  rw [canonical_zero_presentation P B aB (d + e),
    canonical_zero_presentation P B aB d, canonical_zero_presentation P B aB e]
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  let a := P.chartSectionOrientation d (DiagonalPasting.pr d B) aB
    (DiagonalPasting.zero d B) t
  let b := P.chartSectionOrientation e (DiagonalPasting.pr e B) aB
    (DiagonalPasting.zero e B) t
  have hn := compatibleTensorComparison_naturality
    (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B)
    (ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B) F
    (ProEtale.comparisonTensorNatIso P.Coefficient B) a b
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj] at hn
  have hm₁ := congrArg (fun n ↦ n.app (P.diagonalTwistEtale B e))
    (ProEtale.comparison_tensor_app P.Coefficient B (P.diagonalTwistEtale B d))
  have hm₂ := congrArg (fun n ↦ n.app
      (Etale.sectionInvariant P.Coefficient (DiagonalPasting.pr e B)
        (DiagonalPasting.zero e B)))
    (ProEtale.comparison_tensor_app P.Coefficient B
      (Etale.sectionInvariant P.Coefficient (DiagonalPasting.pr d B)
        (DiagonalPasting.zero d B)))
  rw [hm₁, hm₂] at hn
  have hi := compatibleIso_inverse_square _ _ _ _ hn
  dsimp only [compatibleNu, compatibleNuModel, compatibleTensorArrowGeneric,
    modelOrientationPowerMul, compatibleComparisonTensor]
  simp only [Iso.trans_assoc]
  rw [← Functor.mapIso_trans, h, Functor.mapIso_trans]
  simpa only [F, t, a, b, DiagonalPasting.zeroInvariant, Iso.trans_assoc,
    compatibleComparisonTensor,
    compatibleComparisonTensorGeneric, compatibleTensorIso, compatibleTensor] using
    congrArg (fun k ↦ k ≪≫ F.mapIso (compositionEtalePowerAdd P.Coefficient
      P.diagonalExponent P.diagonalExponent_annihilates B d e).symm) hi

end WeilConjectures.PurityFiniteSetting
