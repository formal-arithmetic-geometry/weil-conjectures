/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DualizingUnitComposite

/-! # Ordinary and compared coefficient-unit composition maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Change from the standing tensor-mate unit to the ordinary coefficient-unit origin.
Source: composition proof Step 1, finite site comparison.
(blueprint: new-pur-affine-integration-direct-sum-comparison-maps). -/
def affineIntegrationUnitComparison (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  P.modelOrientationUnit f ≪≫ P.diagonalDualizingComparison f

/-- The ordinary dualizing composite in degree-zero coefficient-unit coordinates.
Source: composition proof Step 1, the tensor mate at the unit.
(blueprint: new-pur-affine-integration-direct-sum-comparison-maps). -/
def affineIntegrationOrdinarySigma (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :=
  (compatibleBifunctorIso (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X)
    (P.chartDualizingUnit f).symm
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (P.chartDualizingUnit g).symm)).hom ≫
    dualizingCompositeSigma P.Coefficient f g ≫ (P.chartDualizingUnit (f ≫ g)).hom

/-- The source comparison for the tensor of two ordinary dualizing objects.
It contains only unit, pullback and monoidal site comparisons; it contains no orientation.
Source: composition proof Step 1, finite site comparison.
(blueprint: new-pur-affine-integration-direct-sum-comparison-maps). -/
def affineIntegrationTensorComparison (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] :=
  P.compatibleTensorIso (P.affineIntegrationUnitComparison f)
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (P.affineIntegrationUnitComparison g) ≪≫
        Dnc.pullComparison P f (P.diagonalOrdinaryDualizing g)) ≪≫
    (compatibleComparisonTensor P.Coefficient X (P.diagonalOrdinaryDualizing f)
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
        (P.diagonalOrdinaryDualizing g))).symm

/-- Ordinary Tate concatenation, including its specified pullback constraint.
Source: composition proof Step 1, ordered even-shifted Tate powers.
(blueprint: new-pur-affine-integration-direct-sum-comparison-maps). -/
def affineIntegrationOrdinaryMu (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y)
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  compatibleBifunctorIso (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X)
    (Iso.refl (P.diagonalTwistEtale X d))
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates
      (Etale.projectiveLineTraceTransport P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level)
        P.Coefficient P.diagonalExponent_annihilates)
      f (P.diagonalExponent_isUnit aY) e) ≪≫
    (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates X d e).symm

end WeilConjectures.PurityFiniteSetting
