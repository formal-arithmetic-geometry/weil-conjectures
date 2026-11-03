/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineIntegrationDirectSumAffineModelFormula
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelSigmaOrdinaryComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineOrdinaryOrientationBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrdinaryOrientationRigidity
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelOrientationPowerPullback
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition

/-! # The ordinary affine zero-section multiplication equation

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-trace/
sec-base-change-and-composition/sk-prop-sp-composition/thm-pur-composition-coherence.proof.md,
Step 1: direct-sum compatibility of integration-normalized vector-bundle purity on the
standard pairs (blueprint: lem-pur-affine-integration-zero-section-ordinary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalTwistEtale
  DiagonalPasting.tensorComparison DiagonalPasting.zeroInvariant

private theorem mapIso_naturality {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a : F ≅ G) {X Y : C} (e : X ≅ Y) :
    a.app X ≪≫ G.mapIso e = F.mapIso e ≪≫ a.app Y := by
  apply Iso.ext
  exact (a.hom.naturality e.hom).symm

/-- Ordinary section orientations multiply under the prescribed affine comparison nu:
`b_(d+e) ∘ nu_(d,e) = m_(d,e) ∘ (b_d ⊗ b_e)`, where `b_r` is the normalized
chartSectionOrientation of the standard zero section and `m_(d,e)` is ordered Tate-power
concatenation (the inverse of `compositionEtalePowerAdd`).
Source: latest blueprint, thm-pur-composition-coherence.proof.md, Step 1: direct-sum
compatibility of integration-normalized vector-bundle purity on the standard pairs
(blueprint: lem-pur-affine-integration-zero-section-ordinary).

Proof:
1. Ordinary coordinate-counit rigidity gives `e_r = γ_r⁻¹` for the integration-transposed
   unit orientation `γ_r` of the rank-r trivial bundle
   (lem-pur-vector-bundle-integration-orientation).
2. Apply the ordinary direct-sum equation of vector-bundle purity to `O^d ⊕ O^e` and
   `K = A_B`, with compositor `c` and first-factor orientation the base change along
   `P_e` of `γ_d` followed by the dualizing tensor map; inverting the orientations gives
   `e_(d+e) σ = M_H (e_q ⊗ q^* e_e)`. The base-change equation of the same corollary
   identifies `e_q` with `j^* e_d` through the exchange (cor-pur-vector-bundle-purity,
   lem-asd-etale-finite-twist-pullback).
3. Pull back along `z = z_(d+e)` and precompose with the two factor comparisons defining
   nu. Naturality of the tensor-pullback isomorphism, the Cartesian first-block square
   (`j z = z_d`) and `q z = z_e` identify the restricted factors with `z_d^* e_d` and
   `z_e^* e_e`, through the same tensor and composition constraints on both sides.
4. Compose with Tate restriction along `z`: tensor and composition compatibility of
   ordinary Tate pullback and the vector-integration base-coefficient composition lemma
   identify the restriction of `M_H` with `m_(d,e)` and the factors with `b_d`, `b_e`
   (`ℓ^n A = 0`, `ℓ` invertible). No block swap is made.
5. Zero ranks: the normalized orientation is the identity and concatenation is the tensor
   unitor; the unit equations of the monoidal pullback comparisons reduce to it. Over the
   empty base all arrows between the zero objects are equal.
-/
theorem affine_integration_zero_section_ordinary (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := P.noetherian aB
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI := DiagonalPasting.affineDimension d B
    letI := DiagonalPasting.affineDimension e B
    letI := DiagonalPasting.affineDimension (d + e) B
    let t := Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates
    DiagonalPasting.nu P.Coefficient P d e B aB ≪≫
        P.chartSectionOrientation (d + e) (DiagonalPasting.pr (d + e) B) aB
          (DiagonalPasting.zero (d + e) B) t =
      compatibleBifunctorIso (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B)
        (P.chartSectionOrientation d (DiagonalPasting.pr d B) aB
          (DiagonalPasting.zero d B) t)
        (P.chartSectionOrientation e (DiagonalPasting.pr e B) aB
          (DiagonalPasting.zero e B) t) ≪≫
      (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates B d e).symm := by
  let := P.noetherian aB
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.2
  let := DiagonalPasting.affineDimension d B
  let := DiagonalPasting.affineDimension e B
  let := DiagonalPasting.affineDimension (d + e) B
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  let ed := P.chartDualizingUnit (DiagonalPasting.pr d B) ≪≫
    P.chartOrdinaryOrientation d (DiagonalPasting.pr d B) aB
  let ee := P.chartDualizingUnit (DiagonalPasting.pr e B) ≪≫
    P.chartOrdinaryOrientation e (DiagonalPasting.pr e B) aB
  let es := P.chartDualizingUnit (DiagonalPasting.pr (d + e) B) ≪≫
    P.chartOrdinaryOrientation (d + e) (DiagonalPasting.pr (d + e) B) aB
  let b := DiagonalPasting.beta P.Coefficient P d
    (DiagonalPasting.affineGeometry d e B).1 (DiagonalPasting.pr d B ≫ aB)
  let eq := b.symm ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.first d e B)).leftDerivedFunctor.mapIso ed
  let eq' := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.q d e B)).leftDerivedFunctor.mapIso ee
  let td := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.first d e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr d B ≫ aB)) d
  let te := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.q d e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr e B ≫ aB)) e
  let z := DiagonalPasting.zero (d + e) B
  let F := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) z).leftDerivedFunctor
  let Fd := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero d B)).leftDerivedFunctor
  let Fe := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero e B)).leftDerivedFunctor
  let ad := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    z (DiagonalPasting.first d e B) (DiagonalPasting.zero d B)
    (DiagonalPasting.affineGeometry d e B).2.1.symm
  let ae := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    z (DiagonalPasting.q d e B) (DiagonalPasting.zero e B)
    (DiagonalPasting.affineGeometry d e B).2.2.1.symm
  let c₁ := ad.app _ ≪≫ F.mapIso b
  let c₂ := ae.app (Etale.dualizingComplex P.Coefficient (DiagonalPasting.pr e B))
  let k₁ := ad.app (P.diagonalTwistEtale (DiagonalPasting.A d B) d)
  let k₂ := ae.app (P.diagonalTwistEtale (DiagonalPasting.A e B) e)
  let D := Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
    z (Etale.dualizingComplex P.Coefficient (DiagonalPasting.q d e B))
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.q d e B)).leftDerivedFunctor.obj
      (Etale.dualizingComplex P.Coefficient (DiagonalPasting.pr e B)))
  let D' := Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
    z ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.first d e B)).leftDerivedFunctor.obj
      (P.diagonalTwistEtale (DiagonalPasting.A d B) d))
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.q d e B)).leftDerivedFunctor.obj
      (P.diagonalTwistEtale (DiagonalPasting.A e B) e))
  let m := (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates (DiagonalPasting.A (d + e) B) d e).symm
  let coeff := DiagonalPasting.tensorComparison P.Coefficient P td te ≪≫ m
  let rs := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t z
    (P.diagonalExponent_isUnit (DiagonalPasting.pr (d + e) B ≫ aB)) (d + e)
  let rd := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero d B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr d B ≫ aB)) d
  let re := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr e B ≫ aB)) e
  let mb := (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates B d e).symm
  let ss := DiagonalPasting.sigma P.Coefficient P d (DiagonalPasting.q d e B)
    (DiagonalPasting.pr e B) (DiagonalPasting.pr (d + e) B ≫ aB) ≪≫
    DiagonalPasting.dualizingCongr P.Coefficient P
      (DiagonalPasting.affineGeometry d e B).2.2.2.1
  have h : ss ≪≫ es = DiagonalPasting.tensorComparison P.Coefficient P eq eq' ≪≫ coeff := by
    simpa only [AffineIntegrationTotalSpaceEquation, ss, Iso.trans_assoc] using
      affine_integration_zero_section_direct_sum_purity P B d e aB
  have hc := affine_integration_zero_section_transport P B d e aB
  change DiagonalPasting.tensorComparison P.Coefficient P k₁ k₂ ≪≫ D'.symm ≪≫
      F.mapIso coeff ≪≫ rs =
    DiagonalPasting.tensorComparison P.Coefficient P rd re ≪≫ mb at hc
  have hf₁ : c₁ ≪≫ F.mapIso eq = Fd.mapIso ed ≪≫ k₁ := by
    dsimp only [c₁, eq]
    simp only [Functor.mapIso_trans, Functor.mapIso_symm,
      Iso.trans_assoc, Iso.self_symm_id_assoc]
    apply Iso.ext
    exact (ad.hom.naturality ed.hom).symm
  have hf₂ : c₂ ≪≫ F.mapIso eq' = Fe.mapIso ee ≪≫ k₂ := by
    exact mapIso_naturality ae ee
  have hn := compatibleTensorComparison_naturality
    (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A (d + e) B))
    (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B) F
    (Etale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} P.Coefficient) z) eq eq'
  have hi : D.symm ≪≫
      F.mapIso (DiagonalPasting.tensorComparison P.Coefficient P eq eq') =
    DiagonalPasting.tensorComparison P.Coefficient P (F.mapIso eq) (F.mapIso eq') ≪≫
      D'.symm := by
    exact compatibleIso_inverse_square _ _ _ _ hn
  have hnu : DiagonalPasting.nu P.Coefficient P d e B aB =
      DiagonalPasting.tensorComparison P.Coefficient P c₁ c₂ ≪≫ D.symm ≪≫ F.mapIso ss := by
    simp only [DiagonalPasting.nu, c₁, c₂, D, F, ss, ad, ae, b, z,
      Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_symm]
  change DiagonalPasting.nu P.Coefficient P d e B aB ≪≫ (F.mapIso es ≪≫ rs) =
    DiagonalPasting.tensorComparison P.Coefficient P
      (Fd.mapIso ed ≪≫ rd) (Fe.mapIso ee ≪≫ re) ≪≫ mb
  calc
    _ = DiagonalPasting.tensorComparison P.Coefficient P c₁ c₂ ≪≫ D.symm ≪≫
        F.mapIso (ss ≪≫ es) ≪≫ rs := by
      rw [hnu]
      simp only [Functor.mapIso_trans, Iso.trans_assoc]
    _ = DiagonalPasting.tensorComparison P.Coefficient P c₁ c₂ ≪≫ D.symm ≪≫
        F.mapIso (DiagonalPasting.tensorComparison P.Coefficient P eq eq' ≪≫ coeff) ≪≫ rs := by
      rw [h]
    _ = DiagonalPasting.tensorComparison P.Coefficient P c₁ c₂ ≪≫
        DiagonalPasting.tensorComparison P.Coefficient P (F.mapIso eq) (F.mapIso eq') ≪≫
        D'.symm ≪≫ F.mapIso coeff ≪≫ rs := by
      simpa only [Functor.mapIso_trans, Iso.trans_assoc] using
        congrArg (fun k ↦ DiagonalPasting.tensorComparison P.Coefficient P c₁ c₂ ≪≫
          k ≪≫ F.mapIso coeff ≪≫ rs) hi
    _ = DiagonalPasting.tensorComparison P.Coefficient P (Fd.mapIso ed) (Fe.mapIso ee) ≪≫
        DiagonalPasting.tensorComparison P.Coefficient P k₁ k₂ ≪≫
        D'.symm ≪≫ F.mapIso coeff ≪≫ rs := by
      have ht := tensorComparison_trans P
        c₁ (F.mapIso eq) c₂ (F.mapIso eq')
      rw [hf₁, hf₂] at ht
      have ht' := tensorComparison_trans P
        (Fd.mapIso ed) k₁ (Fe.mapIso ee) k₂
      simpa only [Iso.trans_assoc] using
        congrArg (fun k ↦ k ≪≫ D'.symm ≪≫ F.mapIso coeff ≪≫ rs) (ht.trans ht'.symm)
    _ = DiagonalPasting.tensorComparison P.Coefficient P (Fd.mapIso ed) (Fe.mapIso ee) ≪≫
        DiagonalPasting.tensorComparison P.Coefficient P rd re ≪≫ mb := by rw [hc]
    _ = _ := by
      rw [← Iso.trans_assoc, tensorComparison_trans]

end WeilConjectures.PurityFiniteSetting
