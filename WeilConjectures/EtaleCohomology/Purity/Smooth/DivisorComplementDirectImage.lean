/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.SixFunctors.Etale.DivisorComplementDirectImage

/-!
# Direct images from the complement of a regular divisor

Let `W` be smooth over an algebraically closed field `k`, `i : D ⟶ W` a regular closed immersion
of codimension one with `D` regular, and `j : U ⟶ W` the complementary open immersion. For a
prime `ℓ` invertible in `k`, the higher direct images of the constant sheaf `ℤ/ℓ` are, near every
point of `D`,

`j_* ℤ/ℓ = ℤ/ℓ`, `R¹j_* ℤ/ℓ = i_* ℤ/ℓ` (that is, `i_* ℤ/ℓ(-1)`, the twist being trivialized by a
primitive `ℓ`-th root of unity of `k`), and `R^q j_* ℤ/ℓ = 0` for `q ≥ 2`

(`AlgebraicGeometry.Etale.HasDivisorComplementDirectImages`).

This follows from purity for the regular immersion `i`
(see
`Etale.exists_nonempty_iso_upperStar_rightDerivedUpperShriek_of_isRegularImmersion`:
`Ri^! (ℤ/ℓ(1)[2]) ≅ ℤ/ℓ` near every point of `D`) and the long exact sequence of cohomology
sheaves of the supported localization triangle `i_* Ri^! L ⟶ L ⟶ Rj_* j^* L ⟶`
(`AlgebraicGeometry.Etale.supportedLocalizationTriangle_mem_distTriang`).

## Main statements

- `AlgebraicGeometry.Etale.exists_hasDivisorComplementDirectImages_of_isRegularImmersion`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Compatibility required from sec-smooth-purity (to be proved there): this is the local form
of `thm-pur-finite-coefficient-smooth-purity` for a regular divisor, with coefficients `ℤ/ℓ`.

**Direct images from the complement of a smooth divisor.** Let `W` be smooth over an
algebraically closed field `k`, `i : D ⟶ W` a regular closed immersion of codimension one with
`D` regular and `j : U ⟶ W` the complementary open immersion. Every point of `D` has an open
neighbourhood `W₀` in `W` over which, writing `j₀ : U ∩ W₀ ⟶ W₀` and `i₀ : D ∩ W₀ ⟶ W₀`,

`R⁰j₀_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j₀_* ℤ/ℓ ≅ i₀_* ℤ/ℓ` and `R^q j₀_* ℤ/ℓ = 0` for `q ≥ 2`.

It follows from purity `Ri^! (ℤ/ℓ(1)[2]) ≅ ℤ/ℓ` near the points of `D`
(`Etale.exists_nonempty_iso_upperStar_rightDerivedUpperShriek_of_isRegularImmersion`),
the localization triangle `i_* Ri^! ℤ/ℓ ⟶ ℤ/ℓ ⟶ Rj_* ℤ/ℓ ⟶` and the trivialization
`μ_ℓ ≅ ℤ/ℓ` over the algebraically closed field `k`. -/
theorem exists_hasDivisorComplementDirectImages_of_isRegularImmersion {k : Type u} [Field k]
    [IsAlgClosed k] {W D U : Scheme.{u}} (aW : W ⟶ Spec (.of k)) [Smooth aW] (i : D ⟶ W)
    [IsRegularImmersion 1 i] (hD : ∀ x : D, IsRegularLocalRing (D.presheaf.stalk x))
    (j : U ⟶ W) [IsOpenImmersion j] (hj : Set.range j = (Set.range i)ᶜ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (x : D) :
    ∃ (W₀ : W.Opens) (_ : i x ∈ W₀),
      HasDivisorComplementDirectImages ℓ (pullback.snd j W₀.ι) (pullback.snd i W₀.ι) := by
  sorry

end AlgebraicGeometry.Etale
