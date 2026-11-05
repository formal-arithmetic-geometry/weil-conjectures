/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.TraceFormula.Supporting.RoosAdjunctionQuotientNormalization
public import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationComparisons
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.TraceFormula.Supporting.TransportedReductionSystemsNormalized
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationsUnique
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Effectivity and simultaneous descent of quotient realization models

Source: Stacks Project, sites-cohomology.tex, Tags 0941 and 06YS; current blueprint,
sec-trace-formula/sk-thm-tf-uniform-formula, integral transport paragraph.
(blueprint: lem-trf-effective-quotient-model-descent).

The ambient assertions keep independent site and coefficient universes. In the
constructibility assertion, u is a common bound for schemes and coefficient fields,
as in the recorded intrinsic constructibility predicate. The small site still has
objects in Type (u+1) and morphisms in Type u. Level n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard CategoryTheory.constantSheaf
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.integralOperationsRoosFunctor WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.sfIntegralConstructible

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

section RoosComparisonUniqueness

-- The computes field uses the defining Roos object, so keep this comparison transparent.
attribute [local semireducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted coefficientSequenceLimit
  integralOperationsRoosFunctor integralOperationsGoodLocalization sfIntegralConstructible

end RoosComparisonUniqueness

universe sa sb sw

section ScalarData
open SheafOfModules
variable {C₀ : Type sa} [Category.{sb} C₀] {J : GrothendieckTopology C₀}
  [J.HasSheafCompose (forget₂ CommRingCat.{sw} RingCat.{sw})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sw}] [HasSheafify J AddCommGrpCat.{sw}]
  [EssentiallySmall.{sw} C₀]

end ScalarData

end WeilConjectures
