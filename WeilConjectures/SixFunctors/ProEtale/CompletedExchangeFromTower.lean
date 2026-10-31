/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.CompleteExchangeMap
public import WeilConjectures.SixFunctors.ProEtale.CompleteDerivedCompletion
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Endpoint transport from the tower exchange.
Source: the final inverse-limit step of
`literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/det-pbc-complete-exchange-iso.proof.md`.
(blueprint: det-pbc-complete-exchange-iso-completion).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

/-- The specified completed exchange is invertible once its tower exchange component is.

The completed map is the composite of the two endpoint comparison isomorphisms with the image
under `R lim` of the tower exchange. Unfolding the definitions and transporting the `IsIso`
instance through whiskering proves this statement. Source: Stacks Project, Tag 0D6J.
(blueprint: det-pbc-complete-exchange-iso-completion).
-/
theorem completedExchange_isIso_of_tower
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (h : IsIso ((towerExchange l E sq.toCommSq).app ((red l E X).obj K))) :
    IsIso (completedExchangeMap l E sq.toCommSq K) := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
