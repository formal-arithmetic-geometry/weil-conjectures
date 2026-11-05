/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import all WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatReductionModel
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.AdjointEquivalenceConjugation.AdjointEquivalenceConjugation

/-!
# Normalized reconstruction and its adjunction calculus

Source: current Weil blueprint, sec-smooth-purity,
prop-pur-adic-reconstruction-trace-coherence, sole proof paragraph
(blueprint: lem-pur-normalized-reconstruction-adjunction-calculus).

All categories are unbounded. The system category, reduction, total limit and their
unit/counit are the recorded evaluation calculus, with its actual projection normalization.
The property Q selects any replete full subcategory; Q = top gives the entire normalized
category. No cohomological, constructibility or Tor-amplitude restriction is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u tX tY tZ v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  normalizedDVRResCompletedComp normalizedDVRKFlatComparison
attribute [local instance 4000] normalizedDVRKFlatReductionModelLocal1
attribute [local instance] normalizedDVRKFlatReductionModelLocal2
  normalizedDVRKFlatReductionModelLocal3

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

variable (hl : IsUnit (l : Γ(W, ⊤))) (S : CoefficientDerivedSystemCalculus l E W)
  (Q : ObjectProperty (coefficientSequenceDerived l E W)) [Q.IsClosedUnderIsomorphisms]

namespace PurReconstruction

variable {C₁ : Type u₁} [Category.{v₁} C₁] {N₁ : Type u₂} [Category.{v₂} N₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {N₂ : Type u₄} [Category.{v₄} N₂]
  {C₃ : Type u₅} [Category.{v₅} C₃] {N₃ : Type u₆} [Category.{v₆} N₃]

end PurReconstruction

end WeilConjectures
