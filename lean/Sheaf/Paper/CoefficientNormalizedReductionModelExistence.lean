/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Existence of the normalized coefficient reduction model

Source: Stacks 06YS, 06YY, 07A4 and 0941
(blueprint: lem-coef-normalized-reduction-model-existence).
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
The sequence projection and scalar-extension construction yields a reduction record
whose tensor presentation is the prescribed one.  The construction uses the normalized
sequence projection adjunction, its finite scalar evaluations, and the actual K-flat
change-of-rings models; the tensor fields are retained definitionally from `T`.
Source: Stacks 06YS, 06YY, 07A4 and 0941.
(blueprint: lem-coef-normalized-reduction-model-existence)
-/
theorem coefficientNormalizedReductionModel_exists
    (T : CoefficientDerivedSystemTensors l E W) :
    ∃ R : CoefficientDerivedSystemReduction l E W,
      R.toCoefficientDerivedSystemTensors = T := by
  sorry

end WeilConjectures
