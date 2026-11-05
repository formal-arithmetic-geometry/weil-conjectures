/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful

/-! # Naturality of the prescribed common-stage right unitor

Source: Stacks Project, Tags 07A4 and 0941; coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-right-unitor-natural).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  commonStageTensorObject

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence commonStageTensorComparison
  operationStageTransitionIso

section Integral
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]

end Integral

-- Compare the cached category instances rather than unfolding their Hom data.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
  Linear.homModule Preadditive.homGroup

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local irreducible] Padic.coefficientExtensionIntegers
  ScalarLocalization.composition pullbackTensorCommonUnit pullbackTensorRationalUnit

attribute [local irreducible] commonStageDerivedTensor rationalDerivedTensor
  pullbackTensorCommonUnitStage pullbackTensorRationalRightUnitor

end WeilConjectures
