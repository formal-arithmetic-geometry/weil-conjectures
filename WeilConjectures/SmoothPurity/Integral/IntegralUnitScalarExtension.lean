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
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorUnit

/-! # Integral scalar extension preserves the tensor unit

Source: Stacks Project, Tags 03EL, 07A4 and 0941
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

/-- Integral scalar extension sends a reduction-normalized unit to a reduction-normalized unit,
compatibly with the integral tensor scalar comparison and with every pair of left (respectively
right) unitors fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941 (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: coherent reduction is fully faithful on the target. Conjugate the system unit
comparison of `systemScalarTensorUnit` by the coherent scalar normalization of
`integralScalarTensorCoherentReduction` and the two unit reductions, and lift it. Both unit
squares become, after reduction, the system unit squares conjugated by the same comparisons. -/
theorem integralUnitScalarExtension
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (UE : sfIntegralConstructibleCategory l E W)
    (uE : (pullbackTensorCalculus l E W).reduction.obj UE.obj ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit)
    (UL : sfIntegralConstructibleCategory l L W)
    (uL : (pullbackTensorCalculus l L W).reduction.obj UL.obj ≅
      (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit) :
    ∃ e : (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj UE ≅ UL,
      (∀ (M : sfIntegralConstructibleCategory l E W)
        (λE : (constructibleIntegralTensor l E W).obj (UE, M) ≅ M)
        (_ : (pullbackTensorCalculus l E W).reduction.map λE.hom.hom =
          (pullbackTensorIntegralReductionTensor l E W UE M).hom ≫
            (pullbackTensorCalculus l E W).systemClosed.tensor.map (Prod.mkHom uE.hom (𝟙 _)) ≫
            ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
              ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom)
        (λL : (constructibleIntegralTensor l L W).obj (UL, (sfConstructibleIntegralScalarExtension
          0 l (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M) ≅
          (sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
        (_ : (pullbackTensorCalculus l L W).reduction.map λL.hom.hom =
          (pullbackTensorIntegralReductionTensor l L W UL _).hom ≫
            (pullbackTensorCalculus l L W).systemClosed.tensor.map (Prod.mkHom uL.hom (𝟙 _)) ≫
            ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor
              ((pullbackTensorCalculus l L W).reduction.obj
                ((sfConstructibleIntegralScalarExtension 0 l
                  (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M).obj)).hom),
        (integralTensorScalarComparison l E L ι W UE M).hom ≫
          (constructibleIntegralTensor l L W).map (Prod.mkHom e.hom (𝟙 _)) ≫ λL.hom =
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map λE.hom) ∧
      (∀ (M : sfIntegralConstructibleCategory l E W)
        (ρE : (constructibleIntegralTensor l E W).obj (M, UE) ≅ M)
        (_ : (pullbackTensorCalculus l E W).reduction.map ρE.hom.hom =
          (pullbackTensorIntegralReductionTensor l E W M UE).hom ≫
            (pullbackTensorCalculus l E W).systemClosed.tensor.map (Prod.mkHom (𝟙 _) uE.hom) ≫
            ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor
              ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom)
        (ρL : (constructibleIntegralTensor l L W).obj ((sfConstructibleIntegralScalarExtension
          0 l (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M, UL) ≅
          (sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
        (_ : (pullbackTensorCalculus l L W).reduction.map ρL.hom.hom =
          (pullbackTensorIntegralReductionTensor l L W _ UL).hom ≫
            (pullbackTensorCalculus l L W).systemClosed.tensor.map (Prod.mkHom (𝟙 _) uL.hom) ≫
            ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor
              ((pullbackTensorCalculus l L W).reduction.obj
                ((sfConstructibleIntegralScalarExtension 0 l
                  (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M).obj)).hom),
        (integralTensorScalarComparison l E L ι W M UE).hom ≫
          (constructibleIntegralTensor l L W).map (Prod.mkHom (𝟙 _) e.hom) ≫ ρL.hom =
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map ρE.hom) := by
  sorry

end WeilConjectures
