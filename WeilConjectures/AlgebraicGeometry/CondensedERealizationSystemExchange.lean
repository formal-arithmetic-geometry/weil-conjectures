/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedERealizationDefinitions
import WeilConjectures.AlgebraicGeometry.CondensedEIntegralExchange
import WeilConjectures.AlgebraicGeometry.CondensedERationalCondensedExchange
@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures
/-- The ordered exchange comparison for any normalized realization system.
Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-system-exchange)
Proof. Construct the integral adjunction mate. Its proved tensor formula is the rational
normalization; the two normalization lemmas supply its ordered ambient image and
continuous realization. Package the map and these three equations. -/
theorem condensedE_realization_system_exchange
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (D : CondensedERealization.Data l E k) :
    Nonempty (CondensedERealization.Exchange l E k D) := by
  refine ⟨{
    integral := fun _ _ _ _ _ _ _ _ _ _ _ _ _ sq ↦
      CondensedERealization.integralMate l E k D sq.toCommSq
    integral_normalization := ?_
    rational_normalization := ?_
    condensed_normalization := ?_ }⟩
  · intro X' X Y' Y g' f' f g _ _ _ _ _ sq K
    exact CondensedERealization.integralMate_normalization l E k D sq K
  · intro X' X Y' Y g' f' f g _ _ _ _ _ sq K
    exact CondensedERealization.integralMate_tensor l E k D sq.toCommSq K
  · intro X' X Y' Y g' f' f g _ _ _ _ _ sq K
    exact CondensedERealization.realizationMate_normalization l E k D sq.toCommSq
      (CategoryTheory.ScalarLocalization.mk K)

end WeilConjectures
