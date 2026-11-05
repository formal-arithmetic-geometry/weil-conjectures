/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedSequenceSemilinear
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearCartesianProjection
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import all WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationTensorChain
import all WeilConjectures.SixFunctors.Supporting.SemilinearTotalTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation

/-! # Components of normalized coefficient evaluation projection

Source: Stacks 07A4, 08J9 and 0941; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-evaluation-projection-components).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local implicit_reducible] CategoryTheory.uniformProd
  coefficientSequenceCommRingSheaf SemilinearSections.systemRing
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition coefficientSequenceEvaluation
  SemilinearSections.evaluation SemilinearSections.ringPresheaf SemilinearSections.rings
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  coefficientSequenceHasDerived Functor.mapHomologicalComplex
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  coefficientTotalTensor coefficientTensorGenerator CoefficientClosedStructure.tensor
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive
  SheafOfModules.monoidalCategory
  coefficientIntegralTensorModelIso coefficientFiniteTensorModelIso
  coefficientSystemTensorModelIso coefficientScalarTensorIso coefficientEvaluationTensorIso
  CoefficientTensorModels.iso coefficientEvaluationSection SemilinearSections.evalSection
  constantSheaf presheafToSheaf Functor.ofSequence Functor.ofOpSequence
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Reuse already typed coefficient-site arguments; Lean's kernel checks the result.
local elab "kernel_exact " t:term : tactic => Lean.Elab.Tactic.withMainContext do
  let e ← Lean.Elab.Term.elabTerm t none
  (← Lean.Elab.Tactic.getMainGoal).assign e
  Lean.Elab.Tactic.replaceMainGoal []

attribute [local instance] coefficientSequenceEvaluation_additive

end WeilConjectures
