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

## Implementation details

The calculus data (reduction adjunction, finite evaluations, tensors, internal-Hom fibers and
sections comparisons) are transported to the generic sequence-site notation of
`EnrichedSequenceProjection`, and `enrichedSequenceProjectionFormula` is applied. The models
`D.globalLimit_model`, `D.globalEvaluation_model` and `D.scalarSections_model` identify the
transported comparisons with the specified ones, and `H.sections_projection` fixes the
system-sections projection; arbitrary evaluation isomorphisms without this equation would not
suffice. Taking H-zero and rewriting the finite counit by `S.counit_projection` gives
`CoefficientHomProjection` for `coefficientGammaZeroMap`. The argument never asserts that
evaluation preserves K-injective systems, or that reducing an integral mapping complex computes
finite internal Hom.

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

/-- Gamma has the actual finite mapping-limit projections and the specified H-zero action.
This is an identity for any calculus with the two recorded projection-model equations,
rather than a new choice
of a mapping equivalence or a construction of the calculus itself. -/
theorem coefficientDerivedSystemProjectionFormulas
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (H : CoefficientDerivedSystemProjectionModels l E W S D) :
    CoefficientGammaProjection l E W S D ∧ CoefficientHomProjection l E W S := by
  exact ⟨coefficientDerivedSystemGammaProjectionTransport l E W S D H,
    coefficientDerivedSystemHomProjectionTransport l E W S D H⟩

end WeilConjectures
