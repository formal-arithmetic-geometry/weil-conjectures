/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelOrientationPowerPullback
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition

/-! # Tate coefficient restriction for the affine direct-sum square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalTwistEtale
  DiagonalPasting.tensorComparison DiagonalPasting.zeroInvariant

private theorem tensorComparison_trans (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))] {X : Scheme.{u}}
    {K K' K'' L L' L'' : DiagonalPasting.D P.Coefficient P X}
    (a : K ≅ K') (a' : K' ≅ K'') (b : L ≅ L') (b' : L' ≅ L'') :
    DiagonalPasting.tensorComparison P.Coefficient P a b ≪≫
        DiagonalPasting.tensorComparison P.Coefficient P a' b' =
      DiagonalPasting.tensorComparison P.Coefficient P (a ≪≫ a') (b ≪≫ b') := by
  apply Iso.ext
  simp only [DiagonalPasting.tensorComparison, Functor.mapIso_trans,
    NatIso.trans_app, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).map a.hom).app L ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj K').map b.hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).map a'.hom).app L' ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj K'').map b'.hom =
    ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).map a.hom).app L ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).map a'.hom).app L ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj K'').map b.hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj K'').map b'.hom
  rw [((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).map a'.hom).naturality_assoc]

/-- Tate coefficient compatibility for the two block projections and their zero sections.
This equation contains no purity orientation or exceptional compositor.
Source: latest blueprint composition proof Step 1, Tate restriction calculation
(blueprint: lem-pur-affine-zero-section-ordered-tate-restriction).

Proof: apply tensor compatibility of ordinary Tate pullback to ordered concatenation
on the total affine space. Move the two block coefficient restrictions through the
monoidal pullback constraint by naturality. The composition law for the coefficient
pullbacks identifies the first block with restriction along z_d and the second with
restriction along z_e. The equations first*z=z_d and q*z=z_e provide their specified
inverse-image compositors. The rank-zero coefficient uses the constant-unit pullback;
the two monoidal unit equations give the same identity in that case. -/
theorem affine_integration_zero_section_transport (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
  letI := P.noetherian aB
  letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
  letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.2
  letI := DiagonalPasting.affineDimension d B
  letI := DiagonalPasting.affineDimension e B
  letI := DiagonalPasting.affineDimension (d + e) B
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  let F := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero (d + e) B)).leftDerivedFunctor
  let cd := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero (d + e) B) (DiagonalPasting.first d e B)
    (DiagonalPasting.zero d B) (DiagonalPasting.affineGeometry d e B).2.1.symm).app
      (P.diagonalTwistEtale (DiagonalPasting.A d B) d)
  let ce := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero (d + e) B) (DiagonalPasting.q d e B)
    (DiagonalPasting.zero e B) (DiagonalPasting.affineGeometry d e B).2.2.1.symm).app
      (P.diagonalTwistEtale (DiagonalPasting.A e B) e)
  let td := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.first d e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr d B ≫ aB)) d
  let te := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.q d e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr e B ≫ aB)) e
  let rd := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero d B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr d B ≫ aB)) d
  let re := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr e B ≫ aB)) e
  let rs := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero (d + e) B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr (d + e) B ≫ aB)) (d + e)
  DiagonalPasting.tensorComparison P.Coefficient P cd ce ≪≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
        (DiagonalPasting.zero (d + e) B) _ _).symm ≪≫
      F.mapIso (DiagonalPasting.tensorComparison P.Coefficient P td te ≪≫
        (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates (DiagonalPasting.A (d + e) B) d e).symm) ≪≫ rs =
    DiagonalPasting.tensorComparison P.Coefficient P rd re ≪≫
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
  let F := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero (d + e) B)).leftDerivedFunctor
  let cd := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero (d + e) B) (DiagonalPasting.first d e B)
    (DiagonalPasting.zero d B) (DiagonalPasting.affineGeometry d e B).2.1.symm).app
      (P.diagonalTwistEtale (DiagonalPasting.A d B) d)
  let ce := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero (d + e) B) (DiagonalPasting.q d e B)
    (DiagonalPasting.zero e B) (DiagonalPasting.affineGeometry d e B).2.2.1.symm).app
      (P.diagonalTwistEtale (DiagonalPasting.A e B) e)
  let td := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.first d e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr d B ≫ aB)) d
  let te := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.q d e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr e B ≫ aB)) e
  let rd := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero d B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr d B ≫ aB)) d
  let re := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero e B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr e B ≫ aB)) e
  let rs := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero (d + e) B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr (d + e) B ≫ aB)) (d + e)
  let RHd := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero (d + e) B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr (d + e) B ≫ aB)) d
  let RHe := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t (DiagonalPasting.zero (d + e) B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr (d + e) B ≫ aB)) e
  let D := Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero (d + e) B)
    (P.diagonalTwistEtale (DiagonalPasting.A (d + e) B) d)
    (P.diagonalTwistEtale (DiagonalPasting.A (d + e) B) e)
  let D' := Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
    (DiagonalPasting.zero (d + e) B)
    ((Etale.ordinaryFinitePullback P.Coefficient (DiagonalPasting.first d e B)).obj
      (P.diagonalTwistEtale (DiagonalPasting.A d B) d))
    ((Etale.ordinaryFinitePullback P.Coefficient (DiagonalPasting.q d e B)).obj
      (P.diagonalTwistEtale (DiagonalPasting.A e B) e))
  let addH := compositionEtalePowerAdd P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates (DiagonalPasting.A (d + e) B) d e
  let addB := compositionEtalePowerAdd P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates B d e
  have hp := power_pullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t (DiagonalPasting.zero (d + e) B)
    (P.diagonalExponent_isUnit (DiagonalPasting.pr (d + e) B ≫ aB)) d e
  change F.mapIso addH ≪≫ D ≪≫
    DiagonalPasting.tensorComparison P.Coefficient P RHd RHe = rs ≪≫ addB at hp
  have hpi := compatibleIso_inverse_square (F.mapIso addH) addB rs
    (D ≪≫ DiagonalPasting.tensorComparison P.Coefficient P RHd RHe) hp.symm
  have hpow : D.symm ≪≫ F.mapIso addH.symm ≪≫ rs =
      DiagonalPasting.tensorComparison P.Coefficient P RHd RHe ≪≫ addB.symm := by
    have hh := congrArg (fun k ↦ D.symm ≪≫ k) hpi
    simpa only [Functor.mapIso_symm, Iso.trans_assoc, Iso.symm_self_id_assoc] using hh
  have hd : cd ≪≫ F.mapIso td ≪≫ RHd = rd := by
    apply Iso.ext
    exact Etale.vectorIntegrationBaseCoefficientPullback_comp P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t (DiagonalPasting.zero (d + e) B)
      (DiagonalPasting.first d e B) (DiagonalPasting.zero d B)
      (DiagonalPasting.affineGeometry d e B).2.1.symm
      (P.diagonalExponent_isUnit (DiagonalPasting.pr d B ≫ aB))
      (P.diagonalExponent_isUnit (DiagonalPasting.pr (d + e) B ≫ aB)) d
  have he : ce ≪≫ F.mapIso te ≪≫ RHe = re := by
    apply Iso.ext
    exact Etale.vectorIntegrationBaseCoefficientPullback_comp P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t (DiagonalPasting.zero (d + e) B)
      (DiagonalPasting.q d e B) (DiagonalPasting.zero e B)
      (DiagonalPasting.affineGeometry d e B).2.2.1.symm
      (P.diagonalExponent_isUnit (DiagonalPasting.pr e B ≫ aB))
      (P.diagonalExponent_isUnit (DiagonalPasting.pr (d + e) B ≫ aB)) e
  have hn := compatibleTensorComparison_naturality
    (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A (d + e) B))
    (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B) F
    (Etale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.zero (d + e) B)) td te
  have hi : D'.symm ≪≫
      F.mapIso (DiagonalPasting.tensorComparison P.Coefficient P td te) =
    DiagonalPasting.tensorComparison P.Coefficient P (F.mapIso td) (F.mapIso te) ≪≫
      D.symm := compatibleIso_inverse_square _ _ _ _ hn
  change DiagonalPasting.tensorComparison P.Coefficient P cd ce ≪≫ D'.symm ≪≫
      F.mapIso (DiagonalPasting.tensorComparison P.Coefficient P td te ≪≫ addH.symm) ≪≫ rs =
    DiagonalPasting.tensorComparison P.Coefficient P rd re ≪≫ addB.symm
  calc
    _ = DiagonalPasting.tensorComparison P.Coefficient P cd ce ≪≫
        DiagonalPasting.tensorComparison P.Coefficient P (F.mapIso td) (F.mapIso te) ≪≫
        D.symm ≪≫ F.mapIso addH.symm ≪≫ rs := by
      simpa only [Functor.mapIso_trans, Iso.trans_assoc] using
        congrArg (fun k ↦ DiagonalPasting.tensorComparison P.Coefficient P cd ce ≪≫
          k ≪≫ F.mapIso addH.symm ≪≫ rs) hi
    _ = DiagonalPasting.tensorComparison P.Coefficient P cd ce ≪≫
        DiagonalPasting.tensorComparison P.Coefficient P (F.mapIso td) (F.mapIso te) ≪≫
        DiagonalPasting.tensorComparison P.Coefficient P RHd RHe ≪≫ addB.symm := by rw [hpow]
    _ = _ := by
      simp only [← Iso.trans_assoc]
      rw [tensorComparison_trans, tensorComparison_trans]
      simp only [Iso.trans_assoc, hd, he]

end WeilConjectures.PurityFiniteSetting
