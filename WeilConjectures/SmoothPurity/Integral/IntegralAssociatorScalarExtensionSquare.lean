/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorCoherentReduction
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorAssociator

/-! # The integral associator commutes with scalar extension

Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The coherently normalized integral associator commutes with the prescribed integral tensor
scalar comparison.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: coherent reduction is fully faithful on the target, so it suffices to compare the
reductions. The coherent scalar-tensor normalization `integralScalarTensorCoherentReduction`
identifies the reduced scalar comparison with the whole-system tensorator, and the defining
reduction equations of both integral associators identify them with the system associators.
The required square of reduced maps is `systemScalarTensorAssociator`. -/
theorem integralAssociatorScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
        (pullbackTensorIntegralAssociator l E W M N P).hom ≫
      (integralTensorScalarComparison l E L ι W M
        ((constructibleIntegralTensor l E W).obj (N, P))).hom ≫
      (constructibleIntegralTensor l L W).map
        (Prod.mkHom (𝟙 ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M))
          (integralTensorScalarComparison l E L ι W N P).hom) =
    (integralTensorScalarComparison l E L ι W
        ((constructibleIntegralTensor l E W).obj (M, N)) P).hom ≫
      (constructibleIntegralTensor l L W).map
        (Prod.mkHom (integralTensorScalarComparison l E L ι W M N).hom
          (𝟙 ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P))) ≫
      (pullbackTensorIntegralAssociator l L W
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj N)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P)).hom := by
  sorry

end WeilConjectures
