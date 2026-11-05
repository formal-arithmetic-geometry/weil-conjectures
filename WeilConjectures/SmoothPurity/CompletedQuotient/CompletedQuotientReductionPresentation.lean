/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # The prescribed ordinary quotient reduction presentation

Source: Stacks 0941 and 06YY; the normalized coherent reduction model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substituteInputs substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  SheafOfModules.monoidalCategory completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] CategoryTheory.Functor.mapHomologicalComplex
  coefficientFiniteDerivedExtension coefficientFiniteDerivedRestriction
  coefficientConstantTowerLimit coefficientConstantTowerEvaluation
  coefficientSequenceLimit
  scalarReductionDerivedRestriction unrestrictedIntegralReductionFunctor
  pullbackTensorOrdinaryLimit pullbackTensorConstantLimit
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralOperationsGoodLocalization
attribute [local implicit_reducible] DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh HomotopyCategory.quotient
  CategoryTheory.Functor.mapHomotopyCategory

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

end WeilConjectures.CompletedQuotient
