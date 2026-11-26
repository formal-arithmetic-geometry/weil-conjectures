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

We construct the core reduction record of a coefficient system, with its prescribed tensor
subrecord and finite quotient calculus.

## Implementation details

The sequence projection derived adjunction is applied to the completed coefficient ring and its
quotient tower and transported across the strict-system sequence equivalence; the transported
unit and counit give the projection equations and one-flat-term K-flat models. The same
change-of-rings construction applied to every finite quotient gives the finite quotient
calculus.

## References

* [Stacks, Tags 06YS, 06YY, 07A4, 07A6, 0941]
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
record with its prescribed tensor subrecord and finite quotient calculus.  The four
representative normalization identities are recorded separately.
-/
theorem coefficientNormalizedReductionCore (T : CoefficientDerivedSystemTensors l E W) :
    ∃ R : CoefficientDerivedSystemReduction l E W,
      R.toCoefficientDerivedSystemTensors = T ∧
      Nonempty (CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) := by
  obtain ⟨R, hR⟩ := coefficientNormalizedReductionModel_exists l E W T
  obtain ⟨Q⟩ := coefficientFiniteQuotientCalculus_exists l E W T
  exact ⟨R, hR, ⟨hR.symm ▸ Q⟩⟩

end WeilConjectures
