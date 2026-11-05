/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import WeilConjectures.SixFunctors.Coefficient.CoefficientPrescribedPairTensorModels
import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarLineData
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorReductionTowerComparison
import WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility

/-! # Normalized derived comparisons for integral lines

(blueprint: lem-pur-integral-line-normalized-derived-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.IntegralOnSlice.abSheafify

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private local instance siteSmall : EssentiallySmall.{u + 1} X.ProEt :=
  scalarReductionSiteSmall.{u, u} X

attribute [-instance] WeilConjectures.integralOperationsFiniteMonoidal
attribute [local instance 30000] SheafOfModules.monoidalCategory

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  HasDerivedCategory.standard coefficientTotalTensor CoefficientClosedStructure.tensor
  CoefficientTensorModels.iso completedIntegralCoefficientSheafUnrestricted constantSheaf

attribute [local semireducible] CoefficientTensorModels.iso

attribute [local semireducible] coefficientTotalTensor

end WeilConjectures.IntegralLineReduction
