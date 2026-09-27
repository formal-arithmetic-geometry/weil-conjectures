/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Vanishing in the universal curve test

This is the positive half of the proof of smooth base change: on the curve-test datum
produced by `AlgebraicGeometry.Etale.exists_curveTestDatum` the higher direct images of the
constant sheaf `Λ/dΛ` vanish. Together with the counterexample chain it gives the
contradiction that proves the theorem.

## Main statements

- `AlgebraicGeometry.Etale.isZero_higherDirectImage_constantSheaf`.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S Y : Scheme.{u}}

/-- Blueprint `sk-thm-vanishing`: Vanishing in the universal curve test.

Let `f : X ⟶ S` be affine smooth of relative dimension one with `X` affine, `S` affine,
integral and normal with algebraically closed function field, let `K` be an algebraically
closed field, `g : Spec K ⟶ S`, and let `d` be invertible on `S`. Then for the Cartesian
square

```
Y ----e----> Spec K
|              |
h              g
v              v
X ----f-----> S
```

the higher direct images `R^q h_* (Λ/dΛ)` of the constant sheaf vanish for every `q ≥ 1`. -/
theorem Etale.isZero_higherDirectImage_constantSheaf (f : X ⟶ S) [IsAffine X] [IsAffine S]
    [IsAffineHom f] [SmoothOfRelativeDimension 1 f] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)) [IsAlgClosed S.functionField]
    (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S) (d : ℕ)
    (hd : IsUnit ((d : ℕ) : Γ(S, ⊤))) (e : Y ⟶ Spec (.of K)) (h : Y ⟶ X)
    (sq : IsPullback e h g f) (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ))))))) :=
  sorry

end AlgebraicGeometry
