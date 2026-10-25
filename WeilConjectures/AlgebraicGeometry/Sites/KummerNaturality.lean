/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Naturality of Kummer classes and restriction of constant sections

For a morphism of schemes `g : X ⟶ Y` and `n` invertible on `Y`, the Kummer boundary
`δ₀ : Γ(Y, 𝒪)ˣ ⟶ H¹(Y, μₙ)` is compatible with pullback: the pullback of `δ₀(a)` to `X`, pushed
along the comparison `g^* μₙ ⟶ μₙ`, is `δ₀(g^* a)`.

For connected schemes `X` and `Y`, the restriction `H⁰(Y, ℤ/n) ⟶ H⁰(X, g^* ℤ/n)` is bijective:
both sides are `ℤ/n`, the constant functions.

## Main statements

- `AlgebraicGeometry.Scheme.sheafH_map_cohomologyMap_kummerδ₀`
- `AlgebraicGeometry.Scheme.bijective_cohomologyMap_zero_constantZMod`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- **Naturality of the Kummer boundary.** For `g : X ⟶ Y`, `n` invertible on `X` and `Y` and a
unit `a` on `Y`, the pullback along `g` of the Kummer class `δ₀(a) ∈ H¹(Y, μₙ)`, pushed along the
comparison `g^* μₙ ⟶ μₙ`, is the Kummer class `δ₀(g^* a) ∈ H¹(X, μₙ)`. -/
theorem sheafH_map_cohomologyMap_kummerδ₀ {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)
    (hY : IsUnit (n : Γ(Y, ⊤))) (hX : IsUnit (n : Γ(X, ⊤))) (a : Γ(Y, ⊤)ˣ) :
    Sheaf.H.map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g) 1
        (Etale.cohomologyMap g (Y.rootsOfUnitySheaf n) 1
          (Y.kummerδ₀ n hY (Additive.ofMul a))) =
      X.kummerδ₀ n hX (Additive.ofMul (Units.map g.appTop.hom a)) := by
  sorry

/-- For connected schemes `X` and `Y`, the restriction map `H⁰(Y, ℤ/n) ⟶ H⁰(X, g^* ℤ/n)` along
any `g : X ⟶ Y` is bijective. -/
theorem bijective_cohomologyMap_zero_constantZMod {X Y : Scheme.{u}} (g : X ⟶ Y)
    [ConnectedSpace X] [ConnectedSpace Y] (n : ℕ) [NeZero n] :
    Function.Bijective (Etale.cohomologyMap g (Y.constantZMod n) 0) := by
  sorry

end AlgebraicGeometry.Scheme
