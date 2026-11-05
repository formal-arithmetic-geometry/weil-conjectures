/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientCompletionRoosTransport
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Nat.Prime.Infinite
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransport

/-! # Completeness under normalized integral coefficient transport

These coefficient equivalences and completeness comparisons are independent of
bounded constructibility and the stratified-perfect characterization.
Source: Stacks 099N; Bhatt--Scholze, Section 6.5
(blueprint: def-pur-completed-coefficient-presentation-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section CoefficientPresentation
variable (W : Scheme.{u})

end CoefficientPresentation

section RestrictionEquivalence
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{u + 1}}

end RestrictionEquivalence

/-- The landed integralDetailedTransport is an equivalence.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: restriction along the inverse coefficient ring isomorphism is an exact
inverse to the landed restriction functor. Both ordinary round trips are identity
on sections. Termwise round trips descend through derived localization, proving
full faithfulness and essential surjectivity of the existing functor. -/
@[instance] theorem purDetailedTransport_isEquivalence (W : Scheme.{u}) :
    (integralDetailedTransport W l E).IsEquivalence := by
  have := restriction_isEquivalence (integralDetailedCoefficientComparison W l E)
  have := (integralDetailedCoefficientRestriction_exact W l E).1
  have := (integralDetailedCoefficientRestriction_exact W l E).2
  exact Functor.isEquivalence_mapDerivedCategory _

end WeilConjectures
