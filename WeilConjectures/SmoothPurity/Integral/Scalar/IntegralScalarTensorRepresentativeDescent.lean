/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.CategoryTheory.SmoothPurity.FunctorSquareRepresentativeDescent
import WeilConjectures.SmoothPurity.Integral.IntegralTensorRepresentativeReassociate

/-! # Descent of an integral scalar tensor representative isomorphism

Source: Stacks 07A4 and 0941; categories.tex, Tag 04VK.
(blueprint: lem-pur-integral-scalar-tensor-representative-descent).
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

attribute [local irreducible] integralOperationsTensorTowerFunctor
  integralOperationsTensorComplexFunctor scalarTensorChain integralCompletedTensor
  integralOperationsRoosFunctor DerivedCategory.Q integralOperationsGoodComplex
attribute [local semireducible] integralOperationsTensorComplexFunctor
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor

variable (W : AlgebraicGeometry.Scheme.{u})
local notation "I" => ObjectProperty.ι (integralOperationsGoodComplex l E W)
local notation "q" => integralOperationsGoodLocalization l E W
local notation "V" => MorphismProperty.inverseImage
  (HomologicalComplex.quasiIso (integralTowerModules l E W) (ComplexShape.up ℤ)) I
local notation "F" => integralOrdinaryDerivedScalar l E L ι W
local notation "S" => Functor.mapHomologicalComplex
  (integralOrdinaryScalar l E L ι W) (ComplexShape.up ℤ)
local notation "k" => ObjectProperty.lift (integralOperationsGoodComplex l L W) (I ⋙ S)
  (fun P ↦ scalarGood l E L ι W P)
local notation "p" => integralOperationsGoodLocalization l L W
local notation "t" => Functor.prod I I ⋙ integralOperationsTensorComplexFunctor l E W
local notation "s" => Functor.prod (ObjectProperty.ι (integralOperationsGoodComplex l L W))
  (ObjectProperty.ι (integralOperationsGoodComplex l L W)) ⋙
    integralOperationsTensorComplexFunctor l L W

end WeilConjectures
