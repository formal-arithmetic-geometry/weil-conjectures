/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing

/-!
# The induction step in relative dimension one

For an affine smooth curve `p : X ⟶ S` the base-change property propagates from degree
`q - 1` to degree `q`. This is the point at which the two lanes of the proof meet: a failure
in degree `q` would produce, by `AlgebraicGeometry.Etale.exists_curveTestDatum`, a curve-test
datum with a nonvanishing higher direct image, which
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constantSheaf` forbids.

## Main statements

- `AlgebraicGeometry.Etale.baseChangeProperty_of_sub_one`.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)

/-- Blueprint `sk-lem-induction`: The induction step in relative dimension one.

Let `p : X ⟶ S` be affine smooth of relative dimension one with `X` affine, and let `n` be
invertible on `S` and annihilate the coefficient ring `Λ`. If `BC(p, Λ, q - 1)` holds for some
`q ≥ 1`, then `BC(p, Λ, q)` holds. -/
theorem Etale.baseChangeProperty_of_sub_one [IsAffine X] [IsAffineHom p]
    [SmoothOfRelativeDimension 1 p] (n : ℕ) (hn : IsUnit ((n : ℕ) : Γ(S, ⊤)))
    (hΛ : (n : Λ) = 0) (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) :
    Etale.BaseChangeProperty Λ p q :=
  sorry

end AlgebraicGeometry
