/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Higher direct images out of a separably closed point

For a separably closed field `K'` and a morphism `t : Spec K' ⟶ S` to an affine scheme, the
higher direct images `R^q t_* (Λ/dΛ)` vanish for `q ≥ 1`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isSepClosed`): for `U` affine and étale
over `S`, the fibre `U ×_S Spec K'` is a finite disjoint union of copies of `Spec K'`, which has
no higher cohomology. This is the vanishing used at the end of the proof of blueprint
`lem-kun-0f1i-normal`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- For `K'` separably closed and `t : Spec K' ⟶ S` with `S` affine, `R^q t_* (Λ/dΛ) = 0` for
every `q ≥ 1`. -/
theorem Etale.isZero_higherDirectImage_of_isSepClosed {K' : Type u} [Field K'] [IsSepClosed K']
    {S : Scheme.{u}} [IsAffine S] (t : Spec (.of K') ⟶ S) (d : ℕ) {q : ℤ} (hq : 1 ≤ q) :
    IsZero (Etale.higherDirectImage Λ t q (Etale.constantModSheaf Λ (Spec (.of K')) d)) :=
  sorry

end AlgebraicGeometry
