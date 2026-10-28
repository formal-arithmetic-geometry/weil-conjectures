/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels

/-! # Normalization component of an integral reduction presentation

This is the sectionwise and derived counit square required by
`ReductionPresentation.normalization`.
(blueprint: lem-sf-integral-hom-reduction-normalization).
(blueprint: lem-sf-integral-hom-models-exist-reduction-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] reductionCounit reductionUnit integralDerivedReduction
  integralReductionChangeOfRings

/-- The normalization witness exists for a fixed target and comparison.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3.
Proof: apply scalar extension and restriction to K-flat representatives. The
ordinary unit is `x ↦ 1 ⊗ x`; balanced tensor associativity gives the invertible
chain comparison and its pure-tensor equation. The derived counit square follows
from the left-derived universal property and the canonical tensor pullback.
-/
theorem reduction_normalization_exists
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ)
    (target : TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) :
    Nonempty {m : ReductionPresentation l E Y D hl a n //
      m.target = target} := by
  sorry

end WeilConjectures.IntegralHom
