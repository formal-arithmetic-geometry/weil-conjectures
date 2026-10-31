/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineIntegrationDirectSumAffineModelFormula

import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineOrdinaryOrientationBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence

/-! # Affine coordinate transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalTwist diagonalTwistEtale diagonalOrdinaryDualizing

/-- The affine coordinate transport identifies the general model formula with the fixed
canonical affine orientation equation.
Source: latest blueprint, composition proof Step 1 (base-change clause of direct-sum
compatibility: the q-orientation is the base change of the rank-d orientation).
(blueprint: new-pur-affine-integration-direct-sum-coordinate-transport).

Proof: the second tensor factors agree: the canonical Gamma is the inverse diagonal
orientation, so the coefficient-unit comparison of pr_e followed by its inverse is the model
orientation of pr_e by definition. It remains to identify the diagonal orientation of q with
modelAffineQOrientation of the canonical family. Both are the coefficient-unit comparison
followed by the site comparison of an ordinary orientation of q; cancel these invertible
components. The ordinary orientation in modelAffineQOrientation is the inverse smooth
base-change mate along the Cartesian square (first, q, pr_d, pr_e), followed by the pullback
of the ordinary diagonal orientation of pr_d and canonical Tate pullback. The diagonal
orientation is the unique normalized one, and its normalization (the coordinate DNC
assembly) is stable under this smooth base change, as in the chart base-change argument;
so the base-changed orientation is normalized for q and equals the diagonal orientation of q
by uniqueness. Rank zero and the empty base are covered by the same uniqueness.
-/
theorem affine_integration_directSum_coordinate_transport (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
    letI := DiagonalPasting.affineDimension e B
    letI := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
    letI := Dnc.compactifiable P (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)
    affineDirectSumModelMap P B d e aB =
      (P.compatibleTensorIso (P.modelAffineQOrientation
        P.modelAffineCanonicalGamma B d e aB)
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (DiagonalPasting.q d e B)).leftDerivedFunctor.mapIso
          (P.modelOrientationUnit (DiagonalPasting.pr e B) ≪≫
            (P.modelAffineCanonicalGamma B aB e).symm))).hom ≫
        (P.modelOrientationMu d e (DiagonalPasting.q d e B)
          (DiagonalPasting.pr e B ≫ aB)).hom := by
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  let := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  let := DiagonalPasting.affineDimension d B
  let := DiagonalPasting.affineDimension e B
  let := Dnc.compactifiable P (DiagonalPasting.pr d B) aB
  let := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
  let := Dnc.compactifiable P (DiagonalPasting.q d e B)
    (DiagonalPasting.pr e B ≫ aB)
  let f := DiagonalPasting.pr d B
  let q := DiagonalPasting.q d e B
  let j := DiagonalPasting.first d e B
  let b := DiagonalPasting.pr e B
  let o := P.chartOrdinaryOrientation d f aB
  let o' := P.chartOrdinaryOrientation d q (b ≫ aB)
  let R := Etale.ordinaryFinitePullback P.Coefficient j
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A (d + e) B)).mapDerivedCategory
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  let T := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aB)) d
  let β := P.chartOrdinaryBaseChange d f aB b q j
    (DiagonalPasting.affineGeometry d e B).1
  have hs : R.mapIso o ≪≫ T = β ≪≫ o' := by
    apply Iso.ext
    exact affine_ordinary_orientation_baseChange P d f aB b q j
      (DiagonalPasting.affineGeometry d e B).1 t
  have hb : β.symm ≪≫ R.mapIso o ≪≫ T = o' := by
    rw [hs, Iso.symm_self_id_assoc]
  have hbC : (C.mapIso β).symm ≪≫ C.mapIso (R.mapIso o) ≪≫ C.mapIso T =
      C.mapIso o' := by
    simpa only [Functor.mapIso_trans, Functor.mapIso_symm] using congrArg C.mapIso hb
  have hn := congrArg (fun i ↦ i ≪≫ C.mapIso T)
    (Dnc.pullComparison_naturality P j o)
  simp only [Iso.trans_assoc] at hn
  have hq : P.modelOrientation d q (b ≫ aB) =
      P.modelAffineQOrientation P.modelAffineCanonicalGamma B d e aB := by
    unfold modelOrientation modelAffineQOrientation
    dsimp only [modelAffineCanonicalGamma]
    rw [(P.chartOrdinaryOrientation_spec d f aB).2,
      (P.chartOrdinaryOrientation_spec d q (b ≫ aB)).2]
    simp only [modelOrientationTwistPullback, Iso.symm_symm_eq, Iso.trans_assoc,
      Functor.mapIso_trans, Functor.mapIso_symm]
    rw [hn]
    erw [Iso.symm_self_id_assoc, Iso.symm_self_id_assoc]
    erw [hbC]
  unfold affineDirectSumModelMap
  rw [hq]
  rfl

end WeilConjectures.PurityFiniteSetting
