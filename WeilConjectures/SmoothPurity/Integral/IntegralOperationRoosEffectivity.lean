/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRepresentativeRoos
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoosComparisonSupplement
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosFiniteReduction
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Effectivity of the strict finite-operation towers

Source: Stacks Tags 099M and 099N(5); Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-pur-integral-operation-roos-effectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] operationDerivedAdjunction operationOrdinaryAdjunction

attribute [local irreducible] scalarReductionDerivedExtension
  coefficientSequenceProjection coefficientSequenceLimit

attribute [local semireducible] coefficientSequenceLimit
attribute [local implicit_reducible] coefficientSequenceLimit
  coefficientConstantTowerEvaluation coefficientFiniteDerivedRestriction
attribute [local irreducible] coefficientConstantTowerLimit coefficientSequenceRestriction
  coefficientRestrictedEvaluationIso coefficientConstantTowerProjection

attribute [local irreducible] operationEffective

attribute [local irreducible] SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

attribute [local irreducible] unrestrictedIntegralComplexFunctor
attribute [local irreducible] scalarReductionExtension coefficientQuotientNatTrans
  unrestrictedIntegralTransition coefficientOrdinaryQuotientComponent coefficientOrdinaryQuotient

attribute [local irreducible] coefficientSequenceEvaluation coefficientSequenceTransition
  unrestrictedIntegralReductionExistence

-- Literal endpoints keep scalar restriction from expanding coefficient actions
-- while comparing evaluation of a composite with successive evaluation.

attribute [local irreducible] operationEvaluationIso

attribute [local irreducible] operationRestrictionIso

attribute [local semireducible] coefficientSequenceRestriction

-- Compare underlying section maps directly; transporting the old functor-level
-- square through scalar restriction would repeatedly unfold completed actions.

attribute [local irreducible] coefficientSequenceRestriction

attribute [local semireducible] operationDerivedAdjunction operationEffective

end WeilConjectures
