/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorSections
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorAssembly
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorKFlat
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationTensorChain

/-! # The ordinary quotient system commutes with total tensor products

Source: Stacks 07A4 (lemma-pullback-tensor-product) and 0941.

For an ordinary quotient-system model `M`, we construct a natural isomorphism of chain
complexes on the ringed sequence site
`M.quotient (P ⊗ Q) ≅ M.quotient P ⊗ M.quotient Q`, whose finite evaluations are the
ordinary scalar tensor comparisons. Both sides are presented levelwise by the finite
scalar extensions of `P ⊗ Q`, compatibly with the strict transitions, and maps of
modules on the sequence site are assembled from compatible finite evaluations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryQuotient

noncomputable section
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension HasDerivedCategory.standard coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology constantSheaf coefficientSequenceEvaluation
  coefficientTotalTensor coefficientTensorGenerator coefficientEvaluationTensorIso
  coefficientScalarTensorIso coefficientSequenceTransition coefficientOrdinaryQuotient

attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat

section Presentation

variable {l E W}
variable {C D : CochainComplex (coefficientSequenceModules l E W) ℤ}
  {T : CochainComplex (scalarReductionSource l E W) ℤ}

end Presentation

end
end OrdinaryQuotient
end WeilConjectures
