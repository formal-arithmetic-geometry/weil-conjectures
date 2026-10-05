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

For an affine smooth curve `p : X ⟶ S`, if the base-change property holds universally in
every degree `< q`, it holds universally in degree `q`. This is the point at which the two
lanes of the proof meet: a universal failure in degree `q` would produce, by
`AlgebraicGeometry.Etale.exists_curveTestDatum`, a curve-test datum with a nonvanishing higher
direct image, which `AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`
forbids.

## Main statements

- `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_forall_lt`: for an affine smooth
  relative curve, the universal base-change property in all degrees `< q` implies it in
  degree `q`.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

/-- Blueprint `sk-lem-induction`: The induction step in relative dimension one.

Let `p : X ⟶ S` be affine smooth of relative dimension one with `X` affine, and let `n` be
invertible on `S` and annihilate the coefficient ring `Λ`. If `BC(p, Λ, q')` holds universally
(after every base change `S' ⟶ S`) for all `q' < q`, where `q ≥ 1`, then `BC(p, Λ, q)` holds
universally. The universal, cumulative hypothesis is needed: the closed–open step of the
reduction (Stacks 0F07) consumes the property after a preliminary base change, which a
fixed-base hypothesis does not supply. Negative degrees in `∀ q' < q` are harmless.

This statement is a recombination of the lemmas of Stacks, Étale Cohomology, Section 59.88
rather than a single tagged one: it is the contradiction between
`AlgebraicGeometry.Etale.exists_curveTestDatum` and
`AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`. -/
theorem Etale.universalBaseChangeProperty_of_forall_lt {q : ℤ}
    (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q') [IsAffine X] [IsAffineHom p]
    [SmoothOfRelativeDimension 1 p] (hq : 1 ≤ q) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    (hΛ : (n : Λ) = 0) :
    Etale.UniversalBaseChangeProperty Λ p q :=
  sorry

end AlgebraicGeometry
