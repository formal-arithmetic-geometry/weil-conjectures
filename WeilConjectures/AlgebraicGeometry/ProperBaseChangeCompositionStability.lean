/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.PrimeInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.TorsionAbelianBaseChange
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Blueprint statements

prop-weil-pbc-composition-stability.
-/

@[expose] public section

universe u_comp

open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Blueprint: prop-weil-pbc-composition-stability. -/
theorem prop_weil_pbc_composition_stability
    {X Y Z : Scheme.{u_comp}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsProper f] [IsProper h]
    (hf : HasAllPrimeInjectiveAcyclicity f)
    (hh : HasAllPrimeInjectiveAcyclicity h) :
    IsProper (f ≫ h) ∧
      HasAllPrimeInjectiveAcyclicity (f ≫ h) ∧
      HasTorsionAbelianBaseChange (f ≫ h) := by
  sorry

end AlgebraicGeometry.Etale
