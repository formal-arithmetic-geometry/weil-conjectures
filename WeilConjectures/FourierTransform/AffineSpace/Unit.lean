/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.AffineSpace.UnitVanishing

/-!
# The Fourier transform of the constant sheaf

On relative affine space `𝔸(n; S)` of dimension `r = #n`, the Fourier–Deligne transform of the
constant sheaf is the skyscraper at the origin, twisted and shifted: `FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

The transform vanishes off the origin
(`AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_affineFourierTransform_unit`), so by the
open–closed triangle it is the direct image of its restriction to the zero section; by the
stalk formula along the zero section that restriction is the compactly supported cohomology
`Rπ_! Λ[r]` of `π : 𝔸(n; S) ⟶ S`, which is `Λ(-r)[-r]` by the affine-space trace
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit`: `FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The Fourier–Deligne transform of the constant sheaf on `𝔸(n; S)` is the skyscraper at
the origin of the dual, Tate twisted and shifted by the relative dimension `r = #n`:

`FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(Λ) ≅ δ₀(-1)[-1]`.

The character must be **nontrivial** in the strong sense that `Ψ 1 - 1` is a unit of `Λ`:
the proof uses `H_c^*(𝔸¹, ℒ_ψ) = 0`, and the `ψ`-isotypic part of `H_c^*(𝔸¹, Λ)` is killed
by `Ψ 1 - 1`. For `Ψ = 1` the kernel is the constant sheaf and the transform of `Λ` is
`Λ(-r)[-r]`, supported everywhere. Asking `Ψ ≠ 1` is not enough when `Λ` is not a domain:
for `Λ = 𝔽_ℓ × 𝔽_ℓ` and `Ψ = (ψ₀, 1)` the transform has the trivial-character transform as a
factor.

Class: torsion; decided by the cohomology of `𝔸^r`, `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-prop-first-formula`) -/
theorem nonempty_iso_affineFourierTransform_unit [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _) ≅
        (shiftFunctor _ (-(Fintype.card n : ℤ))).obj
          ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj
            (skyscraperZero Λ n S))) :=
  sorry


end AlgebraicGeometry.Etale
