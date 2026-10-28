/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Strict reduction tensor comparison and its representative normalization

Source: Stacks 06YS, 06YY, 07A4 and 0941.
(blueprint: lem-coef-strict-reduction-tensor-comparison).
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

/-- The strict reduction functor has a tensor comparison isomorphism.
Source: Stacks 07A4, lemma-pullback-tensor-product, before representative
normalization. The sequence projection pullback is computed on flat-term
K-flat complexes by the ordinary total tensor map; resolving full faithfulness
then descends that map to the specified derived tensor models.
(blueprint: lem-coef-strict-reduction-tensor-comparison). -/
theorem coefficientStrictReductionTensorComparison_exists
    (R : CoefficientDerivedSystemReduction l E W) :
    Nonempty (R.integralClosed.tensor ⋙ R.reduction ≅
      R.reduction.prod R.reduction ⋙ R.systemClosed.tensor) := by
  sorry

/-- A chosen strict reduction comparison has the simultaneous representative
normalization square. This is the normalization part after the comparison map
has been constructed; the finite projections are the prescribed scalar tensor
maps on every flat-term K-flat pair.
Source: Stacks 06YS, 06YY, 07A4 and 0941, representative tensor descent.
(blueprint: lem-coef-strict-reduction-tensor-normalization-fixed). -/
theorem coefficientStrictReductionTensorNormalization_of
    (R : CoefficientDerivedSystemReduction l E W)
    (μ : R.integralClosed.tensor ⋙ R.reduction ≅
      R.reduction.prod R.reduction ⋙ R.systemClosed.tensor) :
    CoefficientReductionTensorNormalization l E W { R with reductionTensor := μ } := by
  sorry

end WeilConjectures
