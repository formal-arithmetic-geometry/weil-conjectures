/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing

/-!
# The induction step in relative dimension one

For an affine smooth curve `p : X ⟶ S` the base-change property propagates from degree
`q - 1` to degree `q`. This is the point at which the two lanes of the proof meet: a failure
in degree `q` would produce, by `AlgebraicGeometry.Etale.exists_curveTestDatum`, a curve-test
datum with a nonvanishing higher direct image, which
`AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf` forbids.

## Main statements

- `AlgebraicGeometry.Etale.BaseChangeProperty.of_sub_one`: for an affine smooth relative
  curve, the base-change property in degree `q - 1` implies it in degree `q`.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

/-- Blueprint `sk-lem-induction`: The induction step in relative dimension one.

Let `p : X ⟶ S` be affine smooth of relative dimension one with `X` affine, and let `n` be
invertible on `S` and annihilate the coefficient ring `Λ`. If `BC(p, Λ, q - 1)` holds for
some `q ≥ 1`, then `BC(p, Λ, q)` holds.

This statement is a recombination of the lemmas of Stacks, Étale Cohomology, Section 59.88
rather than a single tagged one: it is the contradiction between
`AlgebraicGeometry.Etale.exists_curveTestDatum` and
`AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`. -/
theorem Etale.BaseChangeProperty.of_sub_one {q : ℤ}
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [IsAffine X] [IsAffineHom p]
    [SmoothOfRelativeDimension 1 p] (hq : 1 ≤ q) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    (hΛ : (n : Λ) = 0) :
    Etale.BaseChangeProperty Λ p q :=
  sorry

end AlgebraicGeometry
