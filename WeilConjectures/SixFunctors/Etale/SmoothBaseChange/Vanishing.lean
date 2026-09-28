/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum

/-!
# Vanishing in the universal curve test

This is the positive half of the proof of smooth base change: on a curve-test datum
`AlgebraicGeometry.Etale.CurveTestDatum` the higher direct images of the constant sheaf
`Λ/dΛ` along the geometric generic fibre vanish in positive degrees. Together with the
counterexample chain, which produces a curve-test datum where they do not, it gives the
contradiction that proves the theorem.

## Implementation notes

The statement is phrased on a curve-test datum rather than on loose data, so that it is
literally about the same object as `AlgebraicGeometry.Etale.exists_curveTestDatum`. In
particular the geometric point `Spec K ⟶ S₀` of the datum factors through the generic point:
the proof in degree one compares `H¹` of the generic fibre over the function field with `H¹`
over `K` and then spreads a cover out from the generic fibre, neither of which is available
at a closed point.

The sketched proof of the degree-one step works with `H¹` of the constant sheaf with value
`ℤ/dℤ` in the sense of `CategoryTheory.Sheaf.H`, that is, with `AddCommGrpCat`-valued sheaf
cohomology, while the statement below is about `ModuleCat Λ`-valued derived pushforwards, as
in `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor`. The comparison between the two
is not recorded anywhere yet, and is what a file carrying out that step needs first.

## Main statements

- `AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`: on a
  curve-test datum the higher direct images `R^q h_* (Λ/dΛ)` vanish for `q ≥ 1`.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `sk-thm-vanishing`: Vanishing in the universal curve test.

For a curve-test datum `D` — an affine smooth relative curve `f₀ : X₀ ⟶ S₀` over an affine
integral normal base with algebraically closed function field, together with the fibre

```
Y₀ ---e---> Spec K
|              |
h              |
v              v
X₀ ---f₀----> S₀
```

over a geometric generic point and an integer `d` invertible on `S₀` — the higher direct
images `R^q h_* (Λ/dΛ)` of the constant sheaf vanish for every `q ≥ 1`.

This statement is a recombination of the lemmas of Stacks, Étale Cohomology, Section 59.88
rather than a single tagged one: the degree-one case uses the invariance of `H¹` under
extension of algebraically closed base fields together with the spreading theorem
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre`, and the higher
degrees follow by cohomological dimension one of an affine curve. -/
theorem Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf
    (D : Etale.CurveTestDatum.{u}) (q : ℤ) (hq : 1 ≤ q) :
    IsZero (Etale.higherDirectImage Λ D.h q (Etale.constantModSheaf Λ D.Y₀ D.d)) :=
  sorry

end AlgebraicGeometry
