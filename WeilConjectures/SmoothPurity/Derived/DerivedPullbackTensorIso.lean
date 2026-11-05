/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationBilinearComparison
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackTensorNaturality
import WeilConjectures.SmoothPurity.Rational.RationalPullbackTensorAssociatorNaturality
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCompositionCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorUnitCoherence

/-! # Derived pullback and derived tensor comparison

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso).

## Main definitions

* The four `canonical*PullbackTensor` families are the prescribed comparisons.
* The higher coherence predicates state equations on those same comparisons.

## Main statements

* `derivedPullbackTensorIso` packages naturality and the higher compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Preserve the cached additive-group data while comparing stage Hom types.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

-- Match the category-wrapper proof context used by DerivedPullbackTensorHom.
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  integralCoefficientLinear integralScalarConstant sfIntegralCoefficientLinear
  sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  commonStageTensorComparison commonStagePullbackComparison
  operationStageTransitionIso commonStageDerivedTensor commonStageDerivedPullback

section HigherCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

attribute [local irreducible] pullbackTensorIntegralComposition
  pullbackTensorRationalComposition pullbackTensorCommonComposition

attribute [local irreducible] pullbackTensorIntegralReductionTensor
  pullbackTensorIntegralReductionPullback

attribute [local irreducible] pullbackTensorCommonLeft pullbackTensorCommonRight

attribute [local irreducible] pullbackTensorCommonAssociator

attribute [local irreducible] pullbackTensorIntegralUnitReduction

set_option allowUnsafeReducibility true in
attribute [local irreducible] instCategoryDerivedCategory DerivedCategory.instPreadditive
  SheafOfModules.instAbelian SheafOfModules.instCategory

attribute [local irreducible] pullbackTensorIntegralUnit pullbackTensorRationalUnit
  pullbackTensorIntegralLeftUnitor pullbackTensorIntegralRightUnitor
  pullbackTensorRationalLeftUnitor pullbackTensorRationalRightUnitor

attribute [local irreducible] pullbackTensorCommonUnitStage pullbackTensorCommonUnit

attribute [local irreducible] pullbackTensorIntegralAssociator
  pullbackTensorRationalAssociator canonicalIntegralPullbackTensor

section AssociativityNaturality

attribute [local irreducible] sfIntegralConstructible Linear.homModule Preadditive.homGroup

-- Keep the category instances fixed when comparing the finite-stage representatives.
section CommonAssociativity
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

end CommonAssociativity

end AssociativityNaturality

attribute [local irreducible] pullbackTensorIntegralBraiding pullbackTensorRationalBraiding
  rationalDerivedTensor rationalDerivedPullback canonicalRationalPullbackTensor

attribute [local irreducible] sfIntegralConstructible

-- Keep cached category data while comparing representatives over one coefficient field.
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

end HigherCoherence

-- Avoid unfolding completed interfaces while checking the assembly statement.
attribute [local irreducible]
  canonicalCommonStagePullbackTensor
  pullbackTensorIntegralComposition pullbackTensorRationalComposition
  pullbackTensorCommonComposition canonicalIntegralPullbackTensor_composition
  canonicalRationalPullbackTensor_composition canonicalCommonStagePullbackTensor_composition
  pullbackTensorIntegralReductionTensor pullbackTensorIntegralReductionPullback
  canonicalIntegralPullbackTensor_reduction pullbackTensorIntegralAssociator
  pullbackTensorRationalAssociator pullbackTensorIntegralBraiding pullbackTensorRationalBraiding
  pullbackTensorCommonLeft pullbackTensorCommonRight pullbackTensorCommonAssociator
  pullbackTensorCommonBraiding pullbackTensorIntegralUnit pullbackTensorIntegralUnitReduction
  pullbackTensorRationalUnit pullbackTensorIntegralLeftUnitor pullbackTensorRationalLeftUnitor
  pullbackTensorIntegralRightUnitor pullbackTensorRationalRightUnitor
  pullbackTensorRationalScalarUnit pullbackTensorCommonUnit pullbackTensorCommonUnitStage
  pullbackTensorCommonLeftUnitor pullbackTensorCommonRightUnitor
  canonicalIntegralPullbackTensor_unit canonicalRationalPullbackTensor_unit
  canonicalCommonStagePullbackTensor_unit canonicalIntegralPullbackTensor_associative
  canonicalRationalPullbackTensor_associative canonicalCommonStagePullbackTensor_associative
  canonicalIntegralPullbackTensor_braiding canonicalRationalPullbackTensor_braiding
  canonicalCommonStagePullbackTensor_braiding

end WeilConjectures
