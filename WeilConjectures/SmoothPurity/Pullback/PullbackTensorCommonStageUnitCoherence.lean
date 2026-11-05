/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Common.CommonStageTensorRightUnitorNaturality
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorRationalUnitCoherence
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality

/-! Common-stage unit coherence for the completed pullback tensor comparison.

Source: Stacks Project, Tags 07A4 and 0941; the common-stage part of
`lem-pur-pullback-tensor-unit-coherence`.
(blueprint: lem-pur-pullback-tensor-common-stage-unit-coherence)

The proof represents source and target units at a common finite coefficient
field, transports the rational unit equations, and proves independence of the
field by scalar compatibility. Uniqueness is obtained by unit cancellation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open scoped TensorProduct
namespace WeilConjectures

-- Fix the category wrappers before comparing normalized representatives.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  commonStageTensorComparison commonStagePullbackComparison operationStageTransitionIso
  commonStageDerivedTensor commonStageDerivedPullback pullbackTensorCommonUnit
  pullbackTensorCommonUnitStage rationalDerivedPullback
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

section LeftNaturality
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]

end LeftNaturality

attribute [local irreducible] rationalDerivedTensor pullbackTensorRationalUnit
  pullbackTensorRationalLeftUnitor pullbackTensorRationalRightUnitor
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
  Linear.homModule Preadditive.homGroup

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end WeilConjectures
