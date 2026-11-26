/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientStrictReductionTensorComparison

/-! # Strict representative tensor comparison for reduction

## Implementation details

The strict comparison supplied by the sequence projection is chosen first; its simultaneous
representative normalization on arbitrary flat-term K-flat inputs then gives the defining
clauses of the conclusion.

## References

* [Stacks, Tag 06YS]
* [Stacks, Tag 06YY]
* [Stacks, Tag 07A4]
* [Stacks, Tag 0941]
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Reduction admits a tensor comparison computed by a single strict chain map. -/
theorem coefficientStrictReductionTensorNormalization
    (R : CoefficientDerivedSystemReduction l E W) :
    ∃ μ : R.integralClosed.tensor ⋙ R.reduction ≅
      R.reduction.prod R.reduction ⋙ R.systemClosed.tensor,
      CoefficientReductionTensorNormalization l E W { R with reductionTensor := μ } := by
  exact coefficientStrictReductionTensorNormalization_of l E W R

end WeilConjectures
