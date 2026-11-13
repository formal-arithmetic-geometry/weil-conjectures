/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence

/-!
# Open extension by zero and proper derived pushforward
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a proper morphism `p : T ⟶ B` and a quasi-compact open immersion `i : V ⟶ B`,
extension by zero along `i` commutes with proper derived pushforward in their Cartesian
square, on bounded-below derived categories of etale sheaves of modules over a finite
commutative ring. The two projections from `pullback p i` are `b = pullback.fst p i`
and `p_V = pullback.snd p i`. -/
theorem nonempty_iso_etale_open_proper_interchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T B V : Scheme.{u}} (p : T ⟶ B) (i : V ⟶ B)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i] :
    Nonempty
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (pullback.snd p i) ⋙
          (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
            (pullback.fst p i)).mapDerivedCategoryPlus ⋙
          rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p) := by
  obtain ⟨_, γ, _⟩ := properOpenInterchangeCoherence Λ
  exact ⟨γ (pullback.fst p i) i (pullback.snd p i) p pullback.condition⟩

end AlgebraicGeometry.Etale
