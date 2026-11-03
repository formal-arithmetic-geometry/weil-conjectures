/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineIntegrationDirectSumAffineModelFormula
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelSigmaOrdinaryComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineOrdinaryOrientationBaseChange
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrdinaryOrientationRigidity
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts

/-! # Ordinary direct-sum purity before restriction to the zero section

The equation lives on the total affine space, before any section inverse image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalTwist diagonalTwistEtale
  DiagonalPasting.tensorComparison

private theorem ordinaryTensor_trans (P : PurityFiniteSetting.{u})
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

private theorem orientation_congr (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (r : ℕ) (f g : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension r f] [SmoothOfRelativeDimension r g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : f = g) :
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P g aY
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    let F := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    eqToIso (by subst g; rfl) ≪≫
        P.diagonalDualizingObject r g aY =
      P.diagonalDualizingComparison f ≪≫ F.mapIso (P.chartDualizingUnit f).symm ≪≫
        F.mapIso (DiagonalPasting.dualizingCongr P.Coefficient P h ≪≫
          P.chartDualizingUnit g ≪≫ P.chartOrdinaryOrientation r g aY) := by
  let := Dnc.compactifiable P f aY
  let := Dnc.compactifiable P g aY
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  subst g
  simp only [eqToIso_refl, Iso.refl_trans, DiagonalPasting.dualizingCongr,
    Functor.mapIso_trans, Functor.mapIso_symm, Iso.symm_self_id_assoc]
  have hh := (P.chartOrdinaryOrientation_spec r f aY).2
  simpa only [Functor.mapIso_trans, Iso.trans_assoc] using hh

/-- The ordinary total-space direct-sum equation, with the first orientation obtained
by the specified Cartesian base-change mate. No zero section occurs in this equation.
Source: latest blueprint composition proof Step 1
(blueprint: lem-pur-affine-integration-zero-section-direct-sum-purity). -/
def AffineIntegrationTotalSpaceEquation (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] : Prop :=
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
  DiagonalPasting.sigma P.Coefficient P d (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B) (DiagonalPasting.pr (d + e) B ≫ aB) ≪≫
    DiagonalPasting.dualizingCongr P.Coefficient P
      (DiagonalPasting.affineGeometry d e B).2.2.2.1 ≪≫ es =
  DiagonalPasting.tensorComparison P.Coefficient P eq eq' ≪≫
    DiagonalPasting.tensorComparison P.Coefficient P td te ≪≫
    (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates (DiagonalPasting.A (d + e) B) d e).symm

end WeilConjectures.PurityFiniteSetting
