/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModelExistence
import WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteQuotientCalculusExistence

/-! # Core normalized coefficient reduction witness

## References

* [Stacks, Tag 06YS]
* [Stacks, Tag 06YY]
* [Stacks, Tag 07A4]
* [Stacks, Tag 07A6]
* [Stacks, Tag 0941]
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
The sequence projection and scalar-extension constructions produce the core reduction
record with its prescribed tensor subrecord and finite quotient calculus.
-/
theorem coefficientNormalizedReductionCore (T : CoefficientDerivedSystemTensors l E W) :
    ∃ R : CoefficientDerivedSystemReduction l E W,
      R.toCoefficientDerivedSystemTensors = T ∧
      Nonempty (CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) := by
  obtain ⟨R, hR⟩ := coefficientNormalizedReductionModel_exists l E W T
  obtain ⟨Q⟩ := coefficientFiniteQuotientCalculus_exists l E W T
  exact ⟨R, hR, ⟨hR.symm ▸ Q⟩⟩

end WeilConjectures
