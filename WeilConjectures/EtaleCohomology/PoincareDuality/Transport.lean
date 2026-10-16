/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.InvertibleTwist

/-!
# Transport through the coefficient stages

The blueprint builds the Poincaré pairing at the finite stages `A_{E,n} = 𝒪_E/ϖ^n` and
carries it to `𝒪_E`, `E` and `ℚ̄_ℓ` by the uniform-tower reconstruction and by descent along
the common-stage construction. In this repository a coefficient stage is a ring `Λ` with the
category `ModuleCat Λ`, the finite reduction along an ideal `J` is the endofunctor
`AlgebraicGeometry.Etale.reductionModIdeal` (`K ↦ K ⊗ᴸ (Λ/J)_X`) of `D(X_ét, Λ)`, and the
`𝒪_E` stage is the derived-complete subcategory `DerivedCategory.derivedCompleteIntegral`.
This file states the genuinely new content of `sk-thm-transport` that the API can express.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_reductionModIdeal`: the derived
  Poincaré pairing of the reduction `K ⊗ᴸ (Λ/J)_X` is perfect, as is that of every complex at a
  finite coefficient ring.

The other ingredients of `sk-thm-transport` are stated where they belong:
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek` and
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar` identify the two
factors of the reduced pairing with the reductions of the two factors of `β_K`, and
`AlgebraicGeometry.Etale.derivedCompleteIntegral_coefficientDual`,
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerShriek` and
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar` place every object of
`β_K` at `Λ = 𝒪_E` in the adic category `D_comp(−, 𝒪_E)`.

## Not stated

- *Change of coefficient ring.* The reduction `A_{E,n} → A_{E,m}` as a change of the ring of
  coefficients, and the comparison of the pairing over `Λ/J` with the reduction of the pairing
  over `Λ`, need a restriction-of-scalars functor between `D(X_ét, Λ)` and `D(X_ét, Λ/J)`,
  which the repository does not have; `reductionModIdeal` stays inside `D(X_ét, Λ)`.
- *The `E` and `ℚ̄_ℓ` stages.* `AlgebraicGeometry.DerivedCategoryDerivedCompleteRational`
  carries no `Rf_!`, and the colimit over finite `E/ℚ_ℓ` does not exist in the repository.
- *The trace isomorphism and the Frobenius statements.* They are built from the pairing and
  the smooth trace, and transport with them; the Frobenius statements belong to
  `sk-thm-frobenius`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y} [HasCompactification a] {d : ℕ}

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**The duality is compatible with finite reduction.** For an ideal `J` of the finite
coefficient ring `Λ`, a Tate orientation `γ` and `K ∈ D(X_ét, Λ)`, the derived Poincaré pairing
`β_{K ⊗ᴸ (Λ/J)}` of the reduction of `K` is perfect. The reduction of a perfect complex need not
be perfect over `Λ`, so this is not an instance of
`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing` for `K ⊗ᴸ (Λ/J)`
itself; it holds because at a finite coefficient ring the derived Poincaré pairing is perfect
for every complex, the Tate twist being invertible
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing_of_finite`). -/
theorem isPerfectPairing_poincarePairing_reductionModIdeal [HasInvertibleExponent Λ X]
    (γ : TateOrientation Λ a d)
    (J : Ideal Λ) (K : DerivedCategoryModule Λ X) :
    IsPerfectPairing (γ.poincarePairing ((reductionModIdeal Λ X J).obj K)) :=
  γ.isPerfectPairing_poincarePairing_of_finite _

end Etale

end AlgebraicGeometry
