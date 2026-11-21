/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullModel
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedPullCompletion

/-! # Strict quotient normalization of completed open pullback

## References

* [Stacks, Tag 099N]
* [Stacks, Tag 0941]
* Bhatt–Scholze, *The pro-étale topology for schemes*, 6.5.8
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The completed open pullback has the published strict quotient-tower model. -/
theorem openFactorPullRealization
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (Pull l E j) := by
  exact IntegralSystemRealization.integralRingedPullCompletion l E j

end WeilConjectures.OpenFactorCoherence
