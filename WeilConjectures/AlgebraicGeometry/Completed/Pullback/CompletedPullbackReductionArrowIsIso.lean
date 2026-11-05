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
(blueprint: lemma-weil-pbc-completed-pullback-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

end AlgebraicGeometry.Scheme
