/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorAssociativity
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # The quotient-system tensor comparison respects the total associators

Source: Stacks 03EK, 07A4 and 0941.

Chain maps of strict systems are tested on all finite evaluations. There the tensor
comparison of the ordinary quotient system becomes the normalized scalar tensor
comparison, whose reassociation is computed in `OrdinaryModel.scalarTensorAssociativity`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

namespace OrdinaryQuotient

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  coefficientEvaluationTensorIso coefficientScalarTensorIso coefficientUniqueComparisonChoice
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology SheafOfModules.monoidalCategory

end OrdinaryQuotient

end WeilConjectures
