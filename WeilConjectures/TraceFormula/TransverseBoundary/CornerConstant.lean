/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.Mathlib.GroupTheory.SpecificGroups.Cyclic
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

open scoped AlgebraicGeometry.Etale

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

/-- Blueprint `det-tf-transverse-corner-constant`, *the restriction* in degree `0`: both
`S - Y_S` and `X_S - z` are connected, so the restriction of the constants is bijective. -/
theorem bijective_cohomologyMap_zero_puncturedTraitι :
    Function.Bijective
      (Etale.cohomologyMap (C.puncturedTraitι zbar)
        ((C.puncturedStrictLocalization zbar).constantZMod ℓ) 0) := by
  sorry

/-- Blueprint `det-tf-transverse-corner-constant`, *the restriction* in degree `1`: the Kummer
class of a local equation of `Y_S` restricts to the Kummer class of a uniformizer of `X_S`,
which is nonzero, so the restriction map is nonzero. -/
theorem cohomologyMap_one_puncturedTraitι_ne_zero :
    Etale.cohomologyMap (C.puncturedTraitι zbar)
      ((C.puncturedStrictLocalization zbar).constantZMod ℓ) 1 ≠ 0 := by
  sorry

omit hℓ hz in
/-- The cohomology of the pullback of the constant sheaf `ℤ/ℓ` along `X_S - z ⟶ S - Y_S` is
that of the constant sheaf `ℤ/ℓ` on `X_S - z`. -/
noncomputable def sheafHUpperStarConstantZModEquiv (q : ℕ) :
    Sheaf.H (((C.puncturedTraitι zbar)^*[AddCommGrpCat.{u + 1}]).obj
      ((C.puncturedStrictLocalization zbar).constantZMod ℓ)) q ≃
      Sheaf.H ((C.puncturedTrait zbar).constantZMod ℓ) q := by
  let e := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (C.puncturedTraitι zbar)).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))
  refine ⟨Sheaf.H.map e.hom q, Sheaf.H.map e.inv q, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  · rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]

/-- Blueprint `det-tf-transverse-corner-constant`: Constant coefficients near a transverse
corner. The restriction map `RΓ(S - Y_S, 𝔽_ℓ) ⟶ RΓ(X_S - z, 𝔽_ℓ)` is an isomorphism: in every
degree `q` the restriction `H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` is bijective. In degree `0`
both sides are the constants of connected schemes; in degrees `q ≥ 2` both sides vanish; in
degree `1` both sides have `ℓ` elements and the map is nonzero (Kummer classes). -/
theorem bijective_cohomologyMap_puncturedTraitι (q : ℕ) :
    Function.Bijective
      (Etale.cohomologyMap (C.puncturedTraitι zbar)
        ((C.puncturedStrictLocalization zbar).constantZMod ℓ) q) := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q
    · exact C.bijective_cohomologyMap_zero_puncturedTraitι zbar hℓ hz
    · obtain ⟨e₁⟩ := C.nonempty_addEquiv_sheafH_puncturedStrictLocalization zbar hℓ hz 1 le_rfl
      obtain ⟨e₂⟩ := C.nonempty_addEquiv_sheafH_puncturedTrait zbar hℓ hz 1 le_rfl
      refine AddMonoidHom.bijective_of_card_eq_prime (p := ℓ) ?_ ?_ _
        (C.cohomologyMap_one_puncturedTraitι_ne_zero zbar hℓ hz)
      · rw [Nat.card_congr e₁.toEquiv, Nat.card_zmod]
      · rw [Nat.card_congr (C.sheafHUpperStarConstantZModEquiv zbar 1), Nat.card_congr e₂.toEquiv, Nat.card_zmod]
  · have := C.subsingleton_sheafH_puncturedStrictLocalization zbar hℓ hz q hq
    have : Subsingleton (Sheaf.H (((C.puncturedTraitι zbar)^*[AddCommGrpCat.{u + 1}]).obj
        ((C.puncturedStrictLocalization zbar).constantZMod ℓ)) q) := by
      have := C.subsingleton_sheafH_puncturedTrait zbar hℓ hz q hq
      exact (C.sheafHUpperStarConstantZModEquiv zbar q).subsingleton
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end AlgebraicGeometry.Scheme.TransverseCorner
