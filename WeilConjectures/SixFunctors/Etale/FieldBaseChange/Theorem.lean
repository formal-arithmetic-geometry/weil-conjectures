/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.Vanishing
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum

/-!
# Base change towards spectra of fields

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K` and `X` a scheme
locally of finite type over `K`. For every `K`-scheme `S'`, every quasi-compact quasi-separated
`g : T ⟶ S'` and every sheaf `F` of `Λ`-modules on `T`, the base-change maps of the cartesian
square

```
X ×_K T --e--> T
   |           |
   h           g
   v           v
X ×_K S' --p--> S'
```

are isomorphisms in every degree
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field`, blueprint `lem-kun-0f1i`).

The proof is by induction on the degree `q`, as in the blueprint. Degree zero is
`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_field`. If the property held
universally below `q ≥ 1` but failed in degree `q`, the analysis of a minimal failure
(`AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage`, blueprint
`lem-kun-0f1d`) would produce an affine `K`-scheme `S''`, an algebraically closed field `K'`
over it and a nonvanishing `R^q h_* (Λ/dΛ)` for `h : X ×_K Spec K' ⟶ X ×_K S''`, which
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_field` (blueprint `lem-kun-0f1i-normal`)
forbids.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0f1i`: base change towards spectra of fields.

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K`, and `a : X ⟶ Spec K`
locally of finite type. Then the base-change property holds universally for `a` in every
degree: for every base change `X' = X ×_K S' ⟶ S'`, every quasi-compact quasi-separated
`g : T ⟶ S'` and every sheaf `F` of `Λ`-modules on `T_ét`, the base-change map
`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism. -/
theorem Etale.universalBaseChangeProperty_of_field [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X : Scheme.{u}} (a : X ⟶ Spec (.of K))
    [LocallyOfFiniteType a] (q : ℤ) :
    Etale.UniversalBaseChangeProperty Λ a q := by
  obtain ⟨n, -, hΛ, hn⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of K))
  suffices H : ∀ m : ℕ, ∀ q : ℤ, q ≤ m → Etale.UniversalBaseChangeProperty Λ a q from
    H q.toNat q (Int.self_le_toNat q)
  intro m
  induction m with
  | zero =>
    intro q hq
    rcases hq.lt_or_eq with hq | rfl
    · exact Etale.universalBaseChangeProperty_of_neg Λ a hq
    · exact Etale.universalBaseChangeProperty_zero_of_field Λ a
  | succ m ih =>
    intro q hq
    rcases (show q ≤ m ∨ q = m + 1 by omega) with hq | rfl
    · exact ih q hq
    by_contra hfail
    obtain ⟨S', X', a', b, p', hpb, _, _, _, _, K', _, _, i, Y, e, h, sq, d, -, hne⟩ :=
      Etale.exists_isPullback_not_isZero_higherDirectImage Λ a n hn hΛ (m + 1) (by omega)
        (fun q' hq' ↦ ih q' (by omega)) hfail
    exact hne (Etale.isZero_higherDirectImage_of_field Λ a a' b p' hpb _ e h sq d
      (by omega))

end AlgebraicGeometry
