/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulConstantTransport
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientFiniteUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Finite reduction of the ordinary-to-completed pullback comparison

Source: Stacks Tag 099N (5).
(blueprint: lem-weil-pbc-completed-pullback-reduced-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

end AlgebraicGeometry.Scheme
