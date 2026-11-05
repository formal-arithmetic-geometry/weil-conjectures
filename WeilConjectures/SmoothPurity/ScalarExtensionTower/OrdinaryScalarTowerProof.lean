/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import all WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRestrictedTower
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionAssociationSuccessor
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationScalarUnits
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationQuotientUnits
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationTensorCoordinates

/-! # Ordinary quotient scalar tower helpers

Section casts, finite comparisons, the assembled scalar tower comparison, its
normalization and fixed scalar models for the ordinary quotient scalar
extension. These private helpers are used, via `import all`, by the ordinary
scalar/pullback calculations.

Source: Stacks 03EK, 03D7, 06YY and 0941, balanced tensor association.
-/

-- All declarations here are private helpers, used by importers via `import all`.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

section OrdinaryQuotientScalarSectionCasts

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
attribute [local implicit_reducible] integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarSectionCasts

section OrdinaryQuotientScalarSections

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
attribute [local implicit_reducible] integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarSections

section OrdinaryQuotientScalarTowerLevels

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralCoefficientCommRingSheaf

attribute [local irreducible] SemilinearSections.systemMap
  CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarTowerLevels

section OrdinaryQuotientScalarTowerConstruction

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralCoefficientCommRingSheaf

attribute [local irreducible] direct directEvaluation finiteComparison

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarTowerConstruction

section OrdinaryQuotientScalarNormalization

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
  SemilinearSections.systemMap CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] direct integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarNormalization

section OrdinaryQuotientScalarModels

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  integralComparisonSequenceScalarModel

end OrdinaryScalarTowerProof
end WeilConjectures

end OrdinaryQuotientScalarModels

end
