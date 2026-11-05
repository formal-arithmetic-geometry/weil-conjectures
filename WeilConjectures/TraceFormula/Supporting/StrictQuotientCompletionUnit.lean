/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismMultiplicationConeDescent
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.TraceFormula.Supporting.StrictQuotientConeAugmentation
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitStrictQuotientModel
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation

/-! # The actual completion unit in the strict quotient cone

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
  CategoryTheory.Limits.limit scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence coefficientSequenceRestriction
  coefficientSequenceEvaluation unrestrictedTowerUnit coefficientConstantTowerLimit

end WeilConjectures
