/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.PrimitiveCounitComparisonModels

/-! # Tensor realization on strict quotient models

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok, together with
strict quotient-system models and normalized Roos descent.
(blueprint: lem-pur-primitive-counit-tensor-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The completed tensor is the total limit of the tensor of coherent reductions,
with its prescribed comparison on every pair of good representatives.
Source: Stacks Tag 0941; steps 1--3 of the primitive comparison argument.
(blueprint: lem-pur-primitive-counit-tensor-realization).

Proof: form the actual quotient-system complexes of the two flat-term K-flat inputs.
Quotient-system flat models give K-flatness, finite evaluation identifications and
strict transition squares. Their tensor represents the system tensor by its K-flat
model. Restrict scalars and apply normalized Roos functor descent to this tower.
Identify the two descended functors by their representative identifications, using
the localization universal property on the product of the good categories. The
result is the required natural isomorphism. On good representatives its equation is
the descent factorization equation composed with the given Roos comparison. The
resolution normalization identifies this Roos comparison with the chosen realization;
this uses equality on resolutions, never equality merely on finite projections.
The argument includes zero inputs, empty schemes, and the first quotient level. -/
theorem primitiveCounitTensorRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
    (S : CoefficientDerivedSystemReduction l E W)
    (ρ : PrimitiveCounit.RoosRealization l E W) :
    ∃ r : integralCompletedTensor l E W ≅
      S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W,
      PrimitiveCounit.TensorModel l E W S ρ r := by sorry

end WeilConjectures
