/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorAssociativity

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

set_option maxHeartbeats 800000 in
-- Instantiating the formal associativity lemma unifies the concrete evaluated tensor terms.
/-- The ordinary tensor comparison of the quotient system is compatible with the native
total associators: both composites agree after every finite evaluation, where they become
the reassociation of the scalar tensor comparisons.
Source: Stacks 03EK, 07A4, 0941. -/
theorem OrdinaryModel.quotientTensor_associativity (M : OrdinaryModel l E W)
    (b : coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W))
    (hb : M.TensorEvaluation l E W b) :
    CoefficientComplexTensorAssociativity (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (M.quotient l E W) b := by
  intro P Q N a b' ha hb'
  apply coefficientSequenceComplex_hom_ext
  intro n
  exact evaluated_tensor_associativity
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W))
    (coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W))
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n))
    (M.quotient l E W) ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ))
    ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ))
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)) b
    (coefficientEvaluationTensorIso l E W n) (coefficientScalarTensorIso l E W n)
    (fun f g ↦ coefficientEvaluationTensorIso_naturality l E W n f g) (fun P Q ↦ hb n P Q)
    P Q N a.hom b'.hom (M.scalarTensorAssociativity l E W n P Q N a ha b' hb')

end OrdinaryQuotient

end WeilConjectures
