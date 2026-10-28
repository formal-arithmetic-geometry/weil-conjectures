/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineBaseChange

/-!
# The projective-line adjunction commutes with base change

For a normalized Tate twist, the projective-line adjunction `Rq_! ⊣ Lq^*(1)[2]` of
`q : ℙ¹_S ⟶ S` (`AlgebraicGeometry.Etale.exists_projectiveLineAdjunction`) commutes with every
base change `S' ⟶ S`, in the sense of
`AlgebraicGeometry.Etale.ProjectiveLineAdjunctionBaseChange` (blueprint `det-sp-p1-adjunction`,
subsection `sk-prop-geo-p1-adjunction`). This is recorded here, for that subsection to prove.

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineAdjunctionBaseChange_of_isNormalized`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Compatibility required from `sk-prop-geo-p1-adjunction` (to be proved there):
blueprint `det-sp-p1-adjunction`.

**The projective-line adjunction commutes with base change.** For a normalized Tate twist and
every scheme `S` on which the exponent of `Λ` is invertible, the adjunctions
`Rq_! ⊣ Lq^*(1)[2]` of the projective line `q : ℙ¹_S ⟶ S` and of its base change along any
`g : S' ⟶ S` have counits compatible with the compact-support base change, in the sense of
`AlgebraicGeometry.Etale.ProjectiveLineAdjunctionBaseChange`: the unit and the counit of the
blueprint are built from the cycle class of the diagonal, the trace, proper base change and the
projection formula, all of which commute with base change. -/
theorem projectiveLineAdjunctionBaseChange_of_isNormalized [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] : ProjectiveLineAdjunctionBaseChange Λ :=
  sorry

end Etale

end AlgebraicGeometry
