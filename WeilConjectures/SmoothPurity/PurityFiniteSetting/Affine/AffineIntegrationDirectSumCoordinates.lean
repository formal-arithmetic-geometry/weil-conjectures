/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelAffineIntegrationOrientationNormalized
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineIntegrationDirectSumAffine
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineIntegrationDirectSumZero

/-! # Direct-sum integration in the specified affine coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The two coordinate bundles satisfy the affine and zero-section direct-sum laws.
Source: latest blueprint, composition proof Step 1, direct-sum integration and its
restriction to zero.
(blueprint: lem-pur-affine-integration-direct-sum-coordinates).

Proof: apply integration-normalized vector purity to the two trivial bundles of ranks
`d` and `e`. Identify their projections and their sum with the prescribed finite-coordinate
models by the maps on their ordered basis vectors. The base-change clause identifies the
first factor with the recorded Cartesian pullback of the rank-d orientation. The ordinary
coefficient-counit normalization writes its coefficient component as theta applied to the
unit component. Transport through vector-integration site comparison; compact-support site
coherence and mate pasting identify the exceptional compositor with the specified one.
Substitute into the ordered direct-sum identity, use naturality of theta, and cancel the
invertible unit components to obtain the affine equation. Pull this equality back along
the total zero section. Pullback tensor coherence, the two zero-section squares and ordered
Tate pullback composition identify its factors with the specified nu, b_d, b_e and power
concatenation, giving the second equation. Rank zero uses the identity adjunction and tensor
unitors; empty bases have unique maps. No sign occurs because all shifts are even. -/
theorem affine_integration_directSum_coordinates (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    ModelAffineOrientationEquation P P.modelAffineCanonicalGamma B d e aB ∧
      ModelZeroOrientationEquation P P.modelAffineCanonicalGamma B d e aB := by
  exact ⟨affine_integration_directSum_affine_helper P B d e aB,
    affine_integration_directSum_zero_helper P B d e aB⟩

end WeilConjectures.PurityFiniteSetting
