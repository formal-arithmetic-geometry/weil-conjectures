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

A first failure of the base-change property in degree `q` can be normalised: after passing to
a field, enlarging it to an algebraically closed field and normalising the base, the failure
is witnessed by a *curve-test datum* — an affine, integral, normal base with algebraically
closed function field, an affine smooth curve over it, and a nonvanishing higher direct image
of a constant sheaf `Λ/dΛ` with `d` dividing `n`.

This is the input to which `AlgebraicGeometry.Etale.isZero_higherDirectImage_constantSheaf`
is applied to obtain a contradiction.

## Main statements

- `AlgebraicGeometry.Etale.exists_curveTestDatum`.

## References

- Stacks Project, Lemma 59.88.7, <https://stacks.math.columbia.edu/tag/0F08>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

/-- Blueprint `sk-lem-universal-datum`: Universal curve-test datum for a failure.

If `BC(p, Λ, q - 1)` holds but `BC(p, Λ, q)` fails, there is a Cartesian square

```
Y₀ ---e---> Spec K
|              |
h              g
v              v
X₀ ---f₀----> S₀
```

with `S₀` affine, integral and normal with algebraically closed function field, `K` an
algebraically closed field, `f₀` affine smooth of relative dimension one with `X₀` affine, and
an integer `d` dividing `n` with `R^q h_* (Λ/dΛ) ≠ 0`. -/
@[stacks 0F08]
theorem Etale.exists_curveTestDatum (n : ℕ) (q : ℤ)
    (hq : Etale.BaseChangeProperty Λ p (q - 1)) (hfail : ¬ Etale.BaseChangeProperty Λ p q) :
    ∃ (S₀ X₀ Y₀ : Scheme.{u}) (_ : IsAffine S₀) (_ : IsAffine X₀) (_ : IsIntegral S₀),
      (∀ x : S₀, IsIntegrallyClosed (S₀.presheaf.stalk x)) ∧
      ∃ (_ : IsAlgClosed S₀.functionField) (f₀ : X₀ ⟶ S₀) (_ : IsAffineHom f₀)
        (_ : SmoothOfRelativeDimension 1 f₀) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
        (g : Spec (.of K) ⟶ S₀) (e : Y₀ ⟶ Spec (.of K)) (h : Y₀ ⟶ X₀)
        (_ : IsPullback e h g f₀) (d : ℕ), d ∣ n ∧
        ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf Y₀.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
                (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ))))))) :=
  sorry

end AlgebraicGeometry
