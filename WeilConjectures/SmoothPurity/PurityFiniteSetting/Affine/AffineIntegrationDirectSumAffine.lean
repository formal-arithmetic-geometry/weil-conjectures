/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelAffineIntegrationOrientationNormalized
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineIntegrationDirectSumAffineCoordinateTransport

/-! # Affine direct-sum coordinate equation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The canonical affine coordinate orientation satisfies the direct-sum mate equation.
Source: latest blueprint, composition proof Step 1 (direct-sum compatibility).
(blueprint: lem-pur-affine-integration-direct-sum-affine-helper).

Proof: unfold ModelAffineOrientationEquation. Its left side, sigma followed by the transported
total orientation, is rewritten by the normalized direct-sum formula in the general
model-orientation coordinates (affine_integration_directSum_model_formula): the tensor of the
diagonal orientations of q and of the second projection, followed by Tate concatenation. The
affine coordinate transport (affine_integration_directSum_coordinate_transport) rewrites this
map into the fixed coordinates of the equation: the base-changed rank-d orientation for q and
the coefficient-unit comparison followed by the inverse canonical Gamma for the second
projection. The two rewrites close the equation.
-/
theorem affine_integration_directSum_affine_helper (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    ModelAffineOrientationEquation P P.modelAffineCanonicalGamma B d e aB := by
  let := DiagonalPasting.affineDimension e B
  unfold ModelAffineOrientationEquation
  rw [affine_integration_directSum_model_formula P B d e aB,
    affine_integration_directSum_coordinate_transport P B d e aB]

end WeilConjectures.PurityFiniteSetting
