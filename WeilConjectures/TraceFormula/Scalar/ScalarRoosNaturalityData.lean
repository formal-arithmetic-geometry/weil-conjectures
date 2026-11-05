/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison

/-! # Natural transformation data for scalar Roos comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction
  integralScalarExtensionOfUniverses completedScalarChangeData

attribute [local implicit_reducible] completedOrdinaryScalarComplex integralOperationsRoos
  integralOperationsRoosFunctor completedScalarRoosEndomorphism
  completedDerivedScalarExtension completedOrdinaryScalarExtension completedScalarCounit
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  integralTowerHasDerivedCategory scalarReductionSourceDerived

section
attribute [local implicit_reducible] coefficientSequenceLimit
end

attribute [local irreducible] coefficientSequenceLimit
attribute [local implicit_reducible] restrictedTower

attribute [local irreducible] completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

end WeilConjectures
