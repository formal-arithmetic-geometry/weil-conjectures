/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationTransport

/-!
# The second projections and the diagonals under `X' ×_{Y'} X' ⟶ X ×_Y X`

For a square `g' ≫ f = f' ≫ g` with induced `e : X' ×_{Y'} X' ⟶ X ×_Y X`
(`AlgebraicGeometry.Etale.IsoSquare.map`), the second projections and the diagonals are
compatible with `e` (`AlgebraicGeometry.Etale.IsoSquare.commSq_snd`,
`AlgebraicGeometry.Etale.IsoSquare.diagonal_comp_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

namespace IsoSquare

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g)

/-- The second projections are compatible with `e : X' ×_{Y'} X' ⟶ X ×_Y X`. -/
lemma commSq_snd : CommSq (map sq) (pullback.snd f' f') (pullback.snd f f) g' :=
  ⟨by simp⟩

/-- The diagonals are compatible with `e : X' ×_{Y'} X' ⟶ X ×_Y X`. -/
lemma diagonal_comp_map : pullback.diagonal f' ≫ map sq = g' ≫ pullback.diagonal f := by
  ext <;> simp

end IsoSquare

end AlgebraicGeometry.Etale
