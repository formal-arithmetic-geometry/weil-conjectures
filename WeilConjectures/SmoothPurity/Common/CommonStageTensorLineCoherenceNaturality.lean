/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful

/-! # Naturality of the common-stage tensor coherence components

Source: Stacks Project, Tags 06YS, 07A4 and 0941; the common-stage paragraph
of the coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-associator-natural).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open CategoryTheory.StageSystem.PairCategory

attribute [local irreducible] Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence commonStageTensorComparison operationStageTransitionIso
  pullbackTensorCommonLeft pullbackTensorCommonRight

-- These constructions are used only through their specifications below.
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue
  integralDerivedPullback integralCompletedTensor integralDerivedInternalHom
  sfRationalScalarExtension integralScalarExtension integralOrdinaryScalar
  rationalDerivedTensor rationalTensorScalarComparison sfIntegralConstructible

end WeilConjectures
