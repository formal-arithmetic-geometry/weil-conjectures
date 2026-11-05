/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationRoosEffectivity
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction

/-! # Ordinary strict quotient tower comparison

Source: Stacks 03CZ, 03EK, 06YY, 08TC and 0941; the strict quotient-cone argument
of `lem-trf-isomorphism-multiplication-cone-descent`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u a b r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 3000] integralTowerHasDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralOperationsGoodComplex coefficientSequenceLimit TrfCompletionRoosNormalized
  integralDerivedPullback integralDerivedPullbackComparison integralPullbackDescent
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory DerivedCategory.Q
  integralOperationsRoosMap

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralComplexFunctor scalarReductionExtension coefficientQuotientNatTrans
  unrestrictedIntegralTransition coefficientOrdinaryQuotientComponent coefficientOrdinaryQuotient
  coefficientSequenceEvaluation coefficientSequenceTransition unrestrictedIntegralReductionExistence

namespace OrdinaryTowerComparisonProof

attribute [local irreducible] operationOrdinaryAdjunction

attribute [local irreducible] operationEvaluationIso

attribute [local irreducible] operationRestrictionIso

-- Compare the actual scalar restrictions, without switching to the older
-- finite-field-indexed completion presentation.

attribute [local irreducible] coefficientSequenceRestriction

attribute [local semireducible] unrestrictedIntegralComplexFunctor

end OrdinaryTowerComparisonProof

attribute [local semireducible] unrestrictedIntegralComplexFunctor

end WeilConjectures
