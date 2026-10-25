/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.TraceFormula.TransverseBoundary.Basic

/-!
# Constant coefficients near a transverse corner

Let `S` be the strict localization of the surface `Z` of a transverse corner
(`AlgebraicGeometry.Scheme.TransverseCorner`) at a geometric point `z̄` over the corner point
`z`, with the two transverse divisors `X_S, Y_S`. For a prime `ℓ` invertible in `k`, both
`RΓ(S - Y_S, 𝔽_ℓ)` and `RΓ(X_S - z, 𝔽_ℓ)` have cohomology `𝔽_ℓ` in degree `0`, `𝔽_ℓ(-1)` in
degree `1` and zero in all other degrees, and the restriction map
`RΓ(S - Y_S, 𝔽_ℓ) ⟶ RΓ(X_S - z, 𝔽_ℓ)` is an isomorphism (blueprint
`det-tf-transverse-corner-constant`). The coefficients are the constant abelian sheaf `ℤ/ℓ`;
the Tate twist `𝔽_ℓ(-1)` is free of rank one over `𝔽_ℓ`, and only its rank is recorded.

## Main definitions

- `AlgebraicGeometry.Scheme.TransverseCorner.puncturedStrictLocalization`: `S - Y_S`, the
  inverse image of `Z - Y` in the strict localization `S`.
- `AlgebraicGeometry.Scheme.TransverseCorner.puncturedTrait`: `X_S - z`, the inverse image of
  `X - z` in `S`.
- `AlgebraicGeometry.Scheme.TransverseCorner.puncturedTraitι`: the closed immersion
  `X_S - z ⟶ S - Y_S`.

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.bijective_cohomologyMap_puncturedTraitι`: the
  restriction `H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` is bijective in every degree.
- `AlgebraicGeometry.Scheme.TransverseCorner.subsingleton_sheafH_puncturedStrictLocalization`,
  `AlgebraicGeometry.Scheme.TransverseCorner.nonempty_addEquiv_sheafH_puncturedStrictLocalization`:
  the cohomology of `S - Y_S`.
- `AlgebraicGeometry.Scheme.TransverseCorner.subsingleton_sheafH_puncturedTrait`,
  `AlgebraicGeometry.Scheme.TransverseCorner.nonempty_addEquiv_sheafH_puncturedTrait`: the
  cohomology of `X_S - z`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (zbar : Spec (.of Ω) ⟶ C.Z)

/-- `S - Y_S`: the inverse image of `Z - Y` in the strict localization `S = Z_(z̄)`. -/
noncomputable abbrev puncturedStrictLocalization : Scheme.{u} :=
  pullback C.j (strictLocalizationToBase zbar)

/-- `X_S - z`: the inverse image of `X - z = X ×_Z (Z - Y)` in `S - Y_S`. -/
noncomputable abbrev puncturedTrait : Scheme.{u} :=
  pullback (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar))

/-- The closed immersion `X_S - z ⟶ S - Y_S`. -/
noncomputable abbrev puncturedTraitι : C.puncturedTrait zbar ⟶ C.puncturedStrictLocalization zbar :=
  pullback.snd _ _

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsAlgClosed k] (hℓ : (ℓ : k) ≠ 0) (hz : Set.range zbar = {C.z})

include hℓ hz

/-- Blueprint `det-tf-transverse-corner-constant`: `H^q(S - Y_S, ℤ/ℓ) = 0` for `q ≥ 2`. -/
theorem subsingleton_sheafH_puncturedStrictLocalization (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H ((C.puncturedStrictLocalization zbar).constantZMod ℓ) q) := by
  sorry

/-- Blueprint `det-tf-transverse-corner-constant`: `H^q(X_S - z, ℤ/ℓ) = 0` for `q ≥ 2`. -/
theorem subsingleton_sheafH_puncturedTrait (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H ((C.puncturedTrait zbar).constantZMod ℓ) q) := by
  sorry

/-- Blueprint `det-tf-transverse-corner-constant`: `H^0(S - Y_S, ℤ/ℓ)` and
`H^1(S - Y_S, ℤ/ℓ) ≅ 𝔽_ℓ(-1)` are free of rank one over `𝔽_ℓ`. -/
theorem nonempty_addEquiv_sheafH_puncturedStrictLocalization (q : ℕ) (hq : q ≤ 1) :
    Nonempty (Sheaf.H ((C.puncturedStrictLocalization zbar).constantZMod ℓ) q ≃+ ZMod ℓ) := by
  sorry

/-- Blueprint `det-tf-transverse-corner-constant`: `H^0(X_S - z, ℤ/ℓ)` and
`H^1(X_S - z, ℤ/ℓ) ≅ 𝔽_ℓ(-1)` are free of rank one over `𝔽_ℓ`. -/
theorem nonempty_addEquiv_sheafH_puncturedTrait (q : ℕ) (hq : q ≤ 1) :
    Nonempty (Sheaf.H ((C.puncturedTrait zbar).constantZMod ℓ) q ≃+ ZMod ℓ) := by
  sorry

/-- Blueprint `det-tf-transverse-corner-constant`: Constant coefficients near a transverse
corner. The restriction map `RΓ(S - Y_S, 𝔽_ℓ) ⟶ RΓ(X_S - z, 𝔽_ℓ)` is an isomorphism: in every
degree `q` the restriction `H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` is bijective. -/
theorem bijective_cohomologyMap_puncturedTraitι (q : ℕ) :
    Function.Bijective
      (Etale.cohomologyMap (C.puncturedTraitι zbar)
        ((C.puncturedStrictLocalization zbar).constantZMod ℓ) q) := by
  sorry

end AlgebraicGeometry.Scheme.TransverseCorner
