/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.FiniteType
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.LimitSquares
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.SepClosedPoint

/-!
# Vanishing of higher direct images along a geometric point of the base

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K`, `X` a scheme locally
of finite type over `K`, `S''` an affine `K`-scheme and `t : Spec K' ⟶ S''` with `K'` separably
closed. For the projection `h : X ×_K Spec K' ⟶ X ×_K S''` the higher direct images
`R^q h_* (Λ/dΛ)` vanish for `q ≥ 1`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_field`).

This is blueprint `lem-kun-0f1i-normal` (without the normality hypothesis, which the argument
does not use). The question is local on `X`, so `X` may be assumed affine. Writing `S''` and
`Spec K'` as limits of spectra of finitely generated `K`-algebras, the base-change maps of the
finite-type stages are isomorphisms
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_finiteType`), hence so is the one of
the limit (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`, blueprint
`lem-kun-0ezt`), whose source `p⁻¹ R^q t_* (Λ/dΛ)` vanishes
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isSepClosed`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0f1i-normal`: for `X` locally of finite type over a field `K`, an affine
`K`-scheme `S''`, a separably closed field `K'` with `t : Spec K' ⟶ S''`, and the projection
`h : X ×_K Spec K' ⟶ X ×_K S''`, the higher direct images `R^q h_* (Λ/dΛ)` vanish for
`q ≥ 1`. -/
theorem Etale.isZero_higherDirectImage_of_field [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X S X' Y : Scheme.{u}} [IsAffine S]
    (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX] (aS : S ⟶ Spec (.of K))
    (b : X' ⟶ X) (p : X' ⟶ S) (_hb : IsPullback b p aX aS)
    {K' : Type u} [Field K'] [IsSepClosed K'] (t : Spec (.of K') ⟶ S)
    (e : Y ⟶ Spec (.of K')) (h : Y ⟶ X') (_sq : IsPullback e h t p) (d : ℕ) {q : ℤ}
    (_hq : 1 ≤ q) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) :=
  sorry

end AlgebraicGeometry
