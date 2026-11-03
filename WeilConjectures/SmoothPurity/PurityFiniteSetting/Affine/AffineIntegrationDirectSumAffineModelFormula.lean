/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelAffineIntegrationOrientationNormalized

/-! # Intermediate direct-sum integration equations -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The orientation map produced by the normalized direct-sum integration calculation,
written in the general model-orientation coordinates.  This is the coefficient-unit
map before identifying the affine coordinate model with the canonical diagonal model.
Source: latest blueprint, composition proof Step 1.
(blueprint: new-pur-affine-integration-direct-sum-model-formula).
-/
def affineDirectSumModelMap (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    [IsSeparated (DiagonalPasting.q d e B)]
    [LocallyOfFiniteType (DiagonalPasting.q d e B)]
    [QuasiCompact (DiagonalPasting.q d e B)]
    [SmoothOfRelativeDimension d (DiagonalPasting.q d e B)]
    [IsSeparated (DiagonalPasting.pr e B)]
    [LocallyOfFiniteType (DiagonalPasting.pr e B)]
    [QuasiCompact (DiagonalPasting.pr e B)]
    [SmoothOfRelativeDimension e (DiagonalPasting.pr e B)] :=
  (P.compatibleTensorIso
    (P.modelOrientation d (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB))
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.q d e B)).leftDerivedFunctor.mapIso
      (P.modelOrientation e (DiagonalPasting.pr e B) aB))).hom ≫
    (P.modelOrientationMu d e (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)).hom

end WeilConjectures.PurityFiniteSetting
