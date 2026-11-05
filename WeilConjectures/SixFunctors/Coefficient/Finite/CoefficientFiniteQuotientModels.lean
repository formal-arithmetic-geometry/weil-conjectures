/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus

/-! # Finite-quotient scalar-extension models

Source: Stacks 06YY and 0941. The canonical finite quotient, its universal derived
scalar extension and its K-flat comparison are re-exported by the evaluation data.
(blueprint: def-coef-finite-quotient-models).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 128
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v a b r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive

section StandardCoefficientInstances

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] preadditiveCoyoneda SheafOfModules.unit
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
attribute [local irreducible] coefficientOrdinaryScalarAdjunction
attribute [local irreducible] coefficientOrdinaryQuotientNaturalTransformation
attribute [local irreducible] scalarReductionExtension
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] coefficientLocalizedCounitModel
attribute [local irreducible] coefficientFiniteReductionModel
attribute [local irreducible] CoefficientComparisonEquation CoefficientTransitionEquation
attribute [local irreducible] coefficientComplexCompositeTransformation
attribute [local irreducible] coefficientComplexCompositeSourceTransformation
attribute [local irreducible] coefficientUniqueComparisonChoice

set_option backward.defeqAttrib.useBackward false

attribute [local irreducible] coefficientKFlatInclusion
  CoefficientTensorModels.iso coefficientBaseChangeHom coefficientEnrichedAdjunctionMap
  CoefficientClosedStructure.tensor CoefficientClosedStructure.transpose
  CoefficientClosedStructure.evaluation CoefficientClosedStructure.composition
  CoefficientReductionModels CoefficientScalarTensorGenerators

attribute [local irreducible] coefficientOrdinaryQuotient
  coefficientOrdinaryQuotientComponent

attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.instCategory HomologicalComplex.instCategory
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  SheafOfModules.siteSheafTensorRight
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex.mapBifunctorMap
  HomologicalComplex₂.total HomologicalComplex.single

set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] coefficientFiniteQuotientExistence

attribute [local irreducible] coefficientFiniteQuotientDerivedExistence

attribute [local irreducible] coefficientFiniteQuotientModel

end StandardCoefficientInstances

end WeilConjectures
