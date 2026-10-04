/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!

# The Fourier–Deligne transform on affine space

The Fourier–Deligne transform of `WeilConjectures.FourierTransform.Defs` is stated for an
arbitrary pair of `S`-schemes with a pairing. Its main case is affine `n`-space `𝔸(n; S)`
paired with itself by the standard pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative
dimension `r = #n`; this file records that datum and the computation of the transform of
the two simplest complexes, the constant sheaf and the skyscraper at the origin.

The affine-space data themselves — the standard pairing, the zero section and the
reflection `x ↦ -x` — are in
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`; they have nothing to do with étale
sheaves.

## Main definitions

- `AlgebraicGeometry.Etale.affineFourierTransform`: the Fourier–Deligne transform of
  `𝔸(n; S)` with the standard pairing.
- `AlgebraicGeometry.Etale.skyscraperZero`: the skyscraper `δ₀` at the origin.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_unit` and
  `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_skyscraperZero`: the transform
  exchanges the constant sheaf and the skyscraper at the origin.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The Fourier–Deligne transform of affine `n`-space over `S`: the transform of
`AlgebraicGeometry.Etale.fourierTransform` for `𝔸(n; S)` paired with itself by the standard
pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative dimension `r = #n`. On the affine
line this is `FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ ℒ_{ψ(xξ)})[1]`. -/
noncomputable def affineFourierTransform (Ψ : AddChar (ZMod p) Λ) :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fourierTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S) (Fintype.card n)

/-- The skyscraper `δ₀` at the origin of `𝔸(n; S)`: the direct image of the constant sheaf
`Λ` along the zero section. -/
noncomputable def skyscraperZero :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)

/-- The Fourier–Deligne transform of the constant sheaf on `𝔸(n; S)` is the skyscraper at
the origin of the dual, Tate twisted and shifted by the relative dimension `r = #n`:

`FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(Λ) ≅ δ₀(-1)[-1]`.

The character must be **nontrivial**: for `Ψ = 1` the kernel is the constant sheaf and the
transform of `Λ` is `Λ(-r)[-r]`, supported everywhere.
(sketch blueprint: `sk-prop-first-formula`) -/
theorem nonempty_iso_fourierTransform_unit [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : Ψ ≠ 1) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _) ≅
        (shiftFunctor _ (-(Fintype.card n : ℤ))).obj
          ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj
            (skyscraperZero Λ n S))) :=
  sorry

/-- The Fourier–Deligne transform of the skyscraper at the origin of `𝔸(n; S)` is the
constant sheaf, shifted by the relative dimension `r = #n`:

`FT_ψ(δ₀) ≅ Λ[r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(δ₀) ≅ Λ[1]`. Unlike
`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_unit` this holds for every character:
the kernel restricted to `{0} ×_S 𝔸(n; S)` is the Artin–Schreier sheaf of the zero function.
(sketch blueprint: `sk-prop-first-formula`) -/
theorem nonempty_iso_fourierTransform_skyscraperZero (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (skyscraperZero Λ n S) ≅
        (shiftFunctor _ (Fintype.card n : ℤ)).obj (𝟙_ _)) :=
  sorry

end AlgebraicGeometry.Etale
