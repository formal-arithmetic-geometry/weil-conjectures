/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismMultiplicationConeDescent
public import WeilConjectures.TraceFormula.Supporting.StrictQuotientConeAugmentation
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Cancellation of the specified comparison on a strict quotient cone

Source: blueprint main-20261015, rational Frobenius integral model, proof (2)--(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit scalarReductionDerivedExistence
  unrestrictedTowerUnit
  unrestrictedIntegralTransition inverseImageReductionProduct

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose integralOperationsRoosFunctor integralOperationsRoos
  integralOperationsPullbackComplexFunctor integralOperationsPullbackTowerFunctor
  trfQuotientTowerFunctor unrestrictedIntegralComplexFunctor
  unrestrictedIntegralReductionFunctor scalarReductionExtension scalarReductionExistence
  unrestrictedIntegralReductionExistence

end WeilConjectures
