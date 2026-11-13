/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReducedUnit
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackFiniteMate

/-! Split result for the finite reduction of completed pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- Every projection-induced arrow in the completed reduction tower is invertible.

Source: Stacks Tag 099N (5), completed-pullback reduction, finite projection clause. -/
theorem completedPullbackReductionArrow_isIso
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic Y d r f hf K C e) :
    ∀ n : ℕ, IsIso (completedPullbackReductionArrow g d K n) := by
  intro n
  have := completedPullbackComparison_reduction_isIso g d r f hf K C e _hK n
  have := completedPullbackComparison_finiteMate_isIso g d K n
  exact IsIso.of_isIso_comp_left
    ((reductionDerivedChange X (completedReductionProjection X d n)).map
      (completedPullbackComparison g d K)) (completedPullbackReductionArrow g d K n)

end AlgebraicGeometry.Scheme
