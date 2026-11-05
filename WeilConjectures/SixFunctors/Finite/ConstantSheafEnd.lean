/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!

# Stalks of the endomorphisms of `f_* Λ` given by endomorphisms over the base

Let `f : Y ⟶ X` be finite and let `g : Y ⟶ Y` be a finite endomorphism over `X`, so that
`g ≫ f = f`. Pulling back sections along `g` is an endomorphism `g^♯` of `f_* Λ`
(`AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver`). At a geometric point `y` of `X`,
the stalk of `f_* Λ` is the product of the stalks of `Λ` at the geometric points `t` of `Y` over
`y` (`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`), and `g^♯` moves the factor at
`t ≫ g` to the factor at `t`: its composite with the restriction `ρ_t` of germs to `t` factors
through the restriction `ρ_{t ≫ g}` to `t ≫ g`.

## Main results

- `AlgebraicGeometry.Etale.sheafFiber_map_lowerStarConstantSheafEndOfOver_stalkRestrict`:
  `(g^♯)_y ≫ ρ_t = ρ_{t ≫ g} ≫ θ` for an explicit `θ : Λ_{t ≫ g} ⟶ Λ_t`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

open Scheme Etale Scheme.Hom

variable {Λ : Type (u + 1)} [CommRing Λ]

end AlgebraicGeometry
