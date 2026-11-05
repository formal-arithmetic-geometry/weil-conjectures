/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel
import WeilConjectures.TraceFormula.Supporting.TransportedReductionScalarNormalized
import all WeilConjectures.TraceFormula.Supporting.AmbientComparisonSystemExistence
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTensorModelNormalization
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence

/-! # Coherent reduction of the scalar tensor comparison

Source: Stacks Project, Tags 07A4, 0941 and 0FPQ.
(blueprint: lem-pur-integral-scalar-tensor-coherent-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel
attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

end WeilConjectures
