/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels

/-! # Target and comparison components of an integral reduction presentation

This isolates the target tensor presentation and its derived comparison from the
normalization field of `ReductionPresentation`.
(blueprint: lem-sf-integral-hom-reduction-target).
(blueprint: lem-sf-integral-hom-models-exist-reduction-components).
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

/-- The finite-level target tensor presentation exists.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3.
Proof: construct the finite-level tensor presentation by scalar extension and
restriction, then use balanced tensor associativity and the derived universal
property to obtain the comparison isomorphism. The remaining sectionwise
normalization is stated separately.
-/
theorem reduction_target_exists
    (n : ℕ) :
    Nonempty (TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) := by
  sorry

end WeilConjectures.IntegralHom
