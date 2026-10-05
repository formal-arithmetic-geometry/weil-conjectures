/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# The universal curve-test datum attached to a failure of base change

A *curve-test datum* (`AlgebraicGeometry.Etale.CurveTestDatum`) is an affine, integral,
normal base `S₀` with algebraically closed function field, an affine smooth relative curve
`f₀ : X₀ ⟶ S₀` over it, the fibre of `f₀` over a geometric generic point
`Spec K ⟶ S₀` of `S₀`, and an integer `d` invertible on `S₀`.

A failure of the universal base-change property in degree `q`, below which it holds
universally, can be normalised to
such a datum: after passing to a field, enlarging it to an algebraically closed field and
normalising the base, the failure is witnessed by a curve-test datum which is a base change of
`p` and whose higher direct image `R^q h_* (Λ/dΛ)` does not vanish, with `d` dividing `n`. This is
`AlgebraicGeometry.Etale.exists_curveTestDatum`; the vanishing theorem
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing`, which forbids exactly that,
is what contradicts it.

## Main definitions

- `AlgebraicGeometry.Etale.CurveTestDatum`: a smooth affine relative curve over a normal
  base with algebraically closed function field, together with its geometric generic fibre
  and a torsion order invertible on the base.

## Main statements

- `AlgebraicGeometry.Etale.exists_curveTestDatum`: a failure of `BC(p, Λ, q)` after some base
  change, when `BC(p, Λ, q')` holds universally for `q' < q`, produces a curve-test datum which is a base change of `p` and on which a higher direct
  image of a constant sheaf fails to vanish.

## References

- Stacks Project, Lemma 59.88.7, <https://stacks.math.columbia.edu/tag/0F08>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A *curve-test datum*: an affine smooth relative curve `f₀ : X₀ ⟶ S₀` over an affine,
integral, normal base with algebraically closed function field, together with its fibre over
a geometric generic point `Spec K ⟶ S₀` and an integer `d` invertible on `S₀`:

```
Y₀ ---e---> Spec K
|              |
h              |
v              v
X₀ ---f₀----> S₀
```

the right-hand column being `Spec` of an extension `i` of the function field of `S₀`
followed by the inclusion of the generic point. Normality of `S₀` is spelled out as integral
closedness of all its stalks, there being no `IsNormal` predicate on schemes. -/
structure Etale.CurveTestDatum where
  /-- the base of the test curve -/
  S₀ : Scheme.{u}
  [isAffine_base : IsAffine S₀]
  [isIntegral_base : IsIntegral S₀]
  /-- the base is normal: all its stalks are integrally closed -/
  isIntegrallyClosed_stalk (x : S₀) : IsIntegrallyClosed (S₀.presheaf.stalk x)
  [isAlgClosed_functionField : IsAlgClosed S₀.functionField]
  /-- the total space of the test curve -/
  X₀ : Scheme.{u}
  /-- the test curve -/
  f₀ : X₀ ⟶ S₀
  [isAffineHom : IsAffineHom f₀]
  [smoothOfRelativeDimension_one : SmoothOfRelativeDimension 1 f₀]
  /-- the algebraically closed field of the geometric generic point -/
  K : Type u
  [field : Field K]
  [isAlgClosed : IsAlgClosed K]
  /-- `K` is an extension of the function field of the base -/
  i : S₀.functionField ⟶ CommRingCat.of K
  /-- the geometric generic fibre of the test curve -/
  Y₀ : Scheme.{u}
  /-- the projection of the fibre to the geometric generic point -/
  e : Y₀ ⟶ Spec (CommRingCat.of K)
  /-- the projection of the fibre to the total space -/
  h : Y₀ ⟶ X₀
  /-- the fibre square is Cartesian -/
  isPullback : IsPullback e h (Spec.map i ≫ S₀.fromSpecStalk (genericPoint S₀)) f₀
  /-- the torsion order -/
  d : ℕ
  /-- the torsion order is invertible on the base -/
  isUnit_d : IsUnit (d : Γ(S₀, ⊤))

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)

/-- Blueprint `sk-lem-universal-datum`: Universal curve-test datum for a failure.

Let `p : X ⟶ S` be an affine smooth relative curve with `X` affine, and let `n` be invertible
on `S` and annihilate `Λ`. Suppose that, for some `q ≥ 1`, `BC(p, Λ, q')` holds universally
(after every base change `S' ⟶ S`) for all `q' < q`, but `BC(p, Λ, q)` does not hold
universally, i.e. it fails after some base change `S' ⟶ S`. Then there is a curve-test datum `D` which is a base
change of `p`, whose torsion order `D.d` divides `n`, and on whose geometric generic fibre
the higher direct image `R^q h_* (Λ/D.d Λ)` of the constant sheaf does not vanish. -/
@[stacks 0F08]
theorem Etale.exists_curveTestDatum [IsAffine X] [IsAffineHom p]
    [SmoothOfRelativeDimension 1 p] (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (hΛ : (n : Λ) = 0)
    (q : ℤ) (hq : 1 ≤ q) (hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q')
    (hfail : ¬ Etale.UniversalBaseChangeProperty Λ p q) :
    ∃ (D : Etale.CurveTestDatum.{u}) (a : D.S₀ ⟶ S) (b : D.X₀ ⟶ X),
      IsPullback b D.f₀ p a ∧ D.d ∣ n ∧
      ¬ IsZero (Etale.higherDirectImage Λ D.h q (Etale.constantModSheaf Λ D.Y₀ D.d)) :=
  sorry

end AlgebraicGeometry
