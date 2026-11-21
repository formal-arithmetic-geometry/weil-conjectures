/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemGammaProjectionTransport
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemHomProjectionTransport

/-! # Actual finite projections of coefficient gamma

The evaluated enriched projection formula and its normalized degree-zero calculation.

## References

* [Stacks, Tag 07A6]
* [Stacks, Tag 08JA]
* [Stacks, Tag 0D6E]
* [Stacks, Tag 0941]
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Gamma has the actual finite mapping-limit projections and the specified H-zero action,
for any calculus with the two recorded projection-model equations. -/
theorem coefficientDerivedSystemProjectionFormulas
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (H : CoefficientDerivedSystemProjectionModels l E W S D) :
    CoefficientGammaProjection l E W S D ∧ CoefficientHomProjection l E W S := by
  exact ⟨coefficientDerivedSystemGammaProjectionTransport l E W S D H,
    coefficientDerivedSystemHomProjectionTransport l E W S D H⟩

end WeilConjectures
