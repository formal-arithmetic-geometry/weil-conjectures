/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTensorLevel
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality
import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! The adjacent transition square for the normalized coherent tensor tower.

Source: Stacks 0941 and 07A4 (blueprint: lem-pur-completed-pullback-tower-level-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v c d r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.leftAdjoint Functor.mapDerivedCategory coefficientSequenceRestriction
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology coefficientTotalTensor coefficientTensorGenerator
  coefficientEvaluationTensorIso SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted scalarReductionExtension

attribute [local semireducible] coefficientTotalTensor

section GeneratorNormalization
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
open MonoidalCategory
open scoped TensorProduct

end GeneratorNormalization

end WeilConjectures
