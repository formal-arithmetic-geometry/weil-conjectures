/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Representative normalizations for coefficient reduction

Source: Stacks 06YS, 06YY, 07A4, 07A6 and 0941
(blueprint: lem-coef-normalized-reduction-models-normalizations).
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
The core reduction construction has the four prescribed tensor normalization
properties: reduction tensor, finite scalar tensor, evaluation tensor, and the
reduction/evaluation comparison.  The quotient calculus supplied by the core
construction is retained as an explicit argument.
Source: Stacks 07A4, 06YY and 0941; proof step 2 of
`lem-coef-normalized-reduction-models`.

Proof plan: use the canonical tensor pullback comparison for the reduction and the
normalized scalar-derived pairs for finite extension.  Evaluate the same comparison
on simultaneous K-flat representatives, where all maps are ordinary pure-tensor
maps.  Uniqueness of the prescribed scalar and evaluation comparisons gives the
three representative squares; evaluating the strict reduction square gives the
fourth identity.  The argument is independent of the final internal-Hom and section
constructions.
(blueprint: lem-coef-normalized-reduction-models-normalizations)
-/
theorem coefficientNormalizedReductionNormalizations
    (T : CoefficientDerivedSystemTensors l E W)
    (R : CoefficientDerivedSystemReduction l E W)
    (hRT : R.toCoefficientDerivedSystemTensors = T)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) :
    CoefficientReductionTensorNormalization l E W R ∧
      CoefficientFiniteTensorNormalization l E W R ∧
      CoefficientEvaluationTensorNormalization l E W R ∧
      CoefficientReductionTensorEvaluation l E W R := by
  sorry

end WeilConjectures
