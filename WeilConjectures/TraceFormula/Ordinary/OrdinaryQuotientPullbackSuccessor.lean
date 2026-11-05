/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift

/-! # Successor compatibility of normalized ordinary pullback comparisons

Source: Stacks 03D2, 0941 and 099N(5), strict quotient-system transitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint limit constantSheaf
  HasDerivedCategory.standard coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingProjectionUnrestricted
  coefficientSequenceCommRingSheaf
  integralComparisonSequenceRingMap scalarReductionExistence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

namespace OrdinarySuccessorProof

section UnderlyingMaps
universe a b c d r
variable {C : Type a} [Category.{b} C] {R : Cᵒᵖ ⥤ RingCat.{r}}

end UnderlyingMaps

section PullbackGeneration
universe a b c d r
variable {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {S : Sheaf J RingCat.{r}} {R R₀ R₁ : Sheaf K RingCat.{r}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R₀)
  (L : SheafOfModules.{r} S ⥤ SheafOfModules.{r} R₀)
  (adj : L ⊣ SheafOfModules.pushforward φ)
  (π : R ⟶ R₀) (β : R ⟶ R₁) (q : R₀ ⟶ R₁) (hq : π ≫ q = β)
  [Presheaf.IsLocallySurjective K π.hom]

end PullbackGeneration

attribute [local irreducible] moduleMap

attribute [local irreducible] restrictedArrow sequenceArrow

attribute [local irreducible] moduleUnit unitSection

end OrdinarySuccessorProof

open OrdinarySuccessorProof

attribute [local irreducible] integralOperationsPullbackGenerator
  unrestrictedIntegralTensorSection

end WeilConjectures
