/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackChainProperties

/-! # Scalar pullback comparison on good representatives

Source: Stacks 07A4 and 0941; categories.tex, Tag 04VK.
(blueprint: lem-pur-integral-scalar-pullback-good-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackComplexFunctor scalarPullbackChain
  integralOperationsRoosFunctor DerivedCategory.Q integralOperationsGoodComplex
attribute [local semireducible] integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor
attribute [local implicit_reducible] integralOperationsPullbackOnGood
  integralOperationsGoodLocalization integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
local notation "I" => ObjectProperty.ι (integralOperationsGoodComplex l E Y)
local notation "S" => Functor.mapHomologicalComplex
  (integralOrdinaryScalar l E L ι Y) (ComplexShape.up ℤ)
local notation "SX" => Functor.mapHomologicalComplex
  (integralOrdinaryScalar l E L ι X) (ComplexShape.up ℤ)
local notation "k" => ObjectProperty.lift (integralOperationsGoodComplex l L Y) (I ⋙ S)
  (fun P ↦ scalarGood l E L ι Y P)
local notation "t" => I ⋙ integralOperationsPullbackComplexFunctor l E f
local notation "s" => ObjectProperty.ι (integralOperationsGoodComplex l L Y) ⋙
  integralOperationsPullbackComplexFunctor l L f

end WeilConjectures
