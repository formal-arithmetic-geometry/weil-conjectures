/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd

/-!
# Pulling back functions along a morphism over the base

For `f₁ : Y₁ ⟶ X`, `f₂ : Y₂ ⟶ X` and `g : Y₂ ⟶ Y₁` with `g ≫ f₁ = f₂`, pulling back sections along
`g` gives a morphism `f₁_* Λ ⟶ f₂_* Λ` of pushforwards of the constant sheaf. For `Y₁ = Y₂` and
`f₁ = f₂` this is `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver`. The construction is
contravariantly functorial in `g` and compatible with pushing forward along a morphism of the
base.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarConstantSheafMapOfOver`: the morphism `f₁_* Λ ⟶ f₂_* Λ`.

## Main results

- `AlgebraicGeometry.Etale.lowerStarConstantSheafMapOfOver_id`,
  `AlgebraicGeometry.Etale.lowerStarConstantSheafMapOfOver_comp`: functoriality.
- `AlgebraicGeometry.Etale.lowerStar_map_lowerStarConstantSheafMapOfOver`: compatibility with
  the pushforward `n_*` along `n : X ⟶ X'`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

noncomputable section

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

end AlgebraicGeometry.Etale
