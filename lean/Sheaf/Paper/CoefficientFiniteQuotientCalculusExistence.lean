/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Existence of the finite quotient calculus

Source: Stacks 06YY, 07A4 and 0941
(blueprint: lem-coef-finite-quotient-calculus-existence).
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
For any tensor presentation, every finite quotient map of the normalized coefficient
rings has its ordinary and derived scalar adjunctions, K-flat preservation, and the
pure-tensor comparison.  These data assemble into the finite quotient calculus.
Source: Stacks 06YY, 07A4 and 0941.
(blueprint: lem-coef-finite-quotient-calculus-existence)
-/
theorem coefficientFiniteQuotientCalculus_exists
    (T : CoefficientDerivedSystemTensors l E W) :
    Nonempty (CoefficientFiniteQuotientCalculus l E W T) := by
  sorry

end WeilConjectures
