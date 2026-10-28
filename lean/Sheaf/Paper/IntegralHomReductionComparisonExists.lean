/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels

/-! # Derived tensor comparison component for integral reduction

This isolates the comparison-isomorphism field required by
`ReductionPresentation`.
(blueprint: lem-sf-integral-hom-reduction-normalization).
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

/-- The derived tensor comparison is available for any fixed finite target.

Source: Stacks Tag 07A4; blueprint order 2478, proof step 3.
Proof: extend both factors to the finite coefficient sheaf on K-flat
representatives. Balanced tensor associativity gives mutually inverse maps;
deriving this comparison yields the displayed natural isomorphism.
-/
theorem reduction_comparison_exists
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ)
    (target : TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) :
    Nonempty (a.tensor ⋙ integralDerivedReduction l E Y D hl n ≅
      ((integralDerivedReduction l E Y D hl n).prod
        (integralDerivedReduction l E Y D hl n)) ⋙ target.tensor) := by
  sorry

end WeilConjectures.IntegralHom
