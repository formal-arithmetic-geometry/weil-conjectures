/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineAdjunctionBaseChange

/-!
# Base change for the projections of projective and affine lines

For every scheme `S` on which the exponent of `Λ` is invertible, the canonical base change maps
`Lg'^* Rp^! ⟶ Rp'^! Lg^*` of the projections `ℙ¹_S ⟶ S` and `𝔸¹_S ⟶ S` are isomorphisms, for
every cartesian square with quasi-compact base change admitting a compactification.

The projective-line case is the formal consequence
`AlgebraicGeometry.Etale.projectiveLineBaseChange_of_adjunction` of the compatibility of the
projective-line adjunction with base change
(`AlgebraicGeometry.Etale.projectiveLineAdjunctionBaseChange_of_isNormalized`), applied to the
normalized Tate twist `μ_n ⊗ Λ` (`AlgebraicGeometry.Etale.hasKummerClass`). The affine line is
the standard chart of `ℙ¹_S`
(`AlgebraicGeometry.Etale.affineLineBaseChange_of_projectiveLineBaseChange`).

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineBaseChange`
- `AlgebraicGeometry.Etale.affineLineBaseChange`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Base change for the projective line.** For every scheme `S` on which the exponent of `Λ`
is invertible and every cartesian square of `q : ℙ¹_S ⟶ S` with quasi-compact base change
admitting a compactification, the base change map `Lg'^* Rq^! ⟶ Rq'^! Lg^*` is an
isomorphism. -/
theorem projectiveLineBaseChange : ProjectiveLineBaseChange Λ := by
  have : NeZero (ringChar Λ) := ⟨CharP.char_ne_zero_of_finite Λ (ringChar Λ)⟩
  let : HasTateTwist Λ := (hasKummerClass Λ).toHasTateTwist
  have : HasTateTwist.IsNormalized Λ := ⟨⟨hasKummerClass Λ, rfl, hasKummerClass_isNormalized Λ⟩⟩
  exact projectiveLineBaseChange_of_adjunction
    (projectiveLineAdjunctionBaseChange_of_isNormalized Λ)

/-- **Base change for the affine-line projections**: for every scheme `S` on which the exponent
of `Λ` is invertible, the base change maps of the projection `𝔸¹_S ⟶ S` are isomorphisms. -/
theorem affineLineBaseChange : AffineLineBaseChange Λ :=
  affineLineBaseChange_of_projectiveLineBaseChange (projectiveLineBaseChange Λ)

end Etale

end AlgebraicGeometry
