/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import all WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryTensorHorizontal
import all WeilConjectures.AlgebraicGeometry.ProjectionTensorCore.SemilinearTensorReductionCore

/-! # Representative square for normalized tensor horizontality

Source: Stacks 07A4 and 0941; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-horizontal-representative).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b c v r w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
namespace WeilConjectures
namespace HorizontalRepresentativeProof
noncomputable section

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence coefficientFiniteQuotientModel
  coefficientFiniteQuotientExtension coefficientFiniteQuotientUnitSection
  SheafOfModules.monoidalCategory scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension coefficientFiniteQuotientDerived HasDerivedCategory.standard
  CoefficientClosedStructure.tensor coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology constantSheaf coefficientSequenceEvaluation
  coefficientTotalTensor coefficientTensorGenerator

attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors CoefficientTensorModels.iso

-- This diagram is independent of coefficient categories and of the chosen resolutions.

end
end HorizontalRepresentativeProof

open HorizontalRepresentativeProof

attribute [local irreducible] coefficientFiniteQuotientDerived HasDerivedCategory.standard
  CoefficientClosedStructure.tensor Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors coefficientTotalTensor coefficientSequenceCommRingSheaf
  coefficientSequenceEvaluation coefficientSystemTensorModelIso coefficientEvaluationTensorIso
  CoefficientTensorModels.iso

attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end WeilConjectures
