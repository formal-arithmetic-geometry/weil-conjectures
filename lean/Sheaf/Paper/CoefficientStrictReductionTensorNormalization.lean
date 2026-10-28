/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Strict representative tensor comparison for reduction

Source: Stacks 06YS, 06YY, 07A4 and 0941.
(blueprint: lem-coef-strict-reduction-tensor-normalization).
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

/-- Reduction admits a tensor comparison computed by a single strict chain map.
Source: Stacks 07A4, proof of lemma-pullback-tensor-product, with the sequence
projection construction of 0941 and the K-flat resolution of 06YS.

Proof: realize reduction as the left derived module pullback along the sequence
projection, transported across the strict-system/sequence-module equivalence.
Use the unique left-adjoint comparison to the specified reduction functor; its
finite projections are fixed by the unit_projection and counit_projection equations.
On flat-term K-flat P and Q, pull back their ordinary total tensor simultaneously.
Pullback preserves flat-term K-flat complexes. The ordinary pullback tensor
isomorphism is one strict chain map, with components the scalar tensor comparison.
The unique pure-generator characterizations identify these components with the
specified coefficientScalarTensorIso and coefficientEvaluationTensorIso.
Transport its natural derived comparison to the given integral and system tensor
models by the fully faithful restriction to K-flat representatives. The defining
descent square is precisely the final system-category equality in the conclusion;
the three pullback presentations give its other clauses. This construction needs
no previously chosen finite or evaluation tensor comparison.
(blueprint: lem-coef-strict-reduction-tensor-normalization). -/
theorem coefficientStrictReductionTensorNormalization
    (R : CoefficientDerivedSystemReduction l E W) :
    ∃ μ : R.integralClosed.tensor ⋙ R.reduction ≅
      R.reduction.prod R.reduction ⋙ R.systemClosed.tensor,
      CoefficientReductionTensorNormalization l E W { R with reductionTensor := μ } := by
  sorry

end WeilConjectures
