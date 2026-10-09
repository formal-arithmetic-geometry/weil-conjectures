/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
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

- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit` and
  `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_skyscraperZero`: the transform
  exchanges the constant sheaf and the skyscraper at the origin.
- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`: the transform for the
  inverse character is the transform of the reflected input.

## Coefficients

Coefficient hypotheses follow the classes in `WeilConjectures.FourierTransform.Defs`.

## Implementation notes

The statements only assert that an isomorphism *exists*. Later uses will need specific,
coherent isomorphisms, which `Classical.choice` cannot provide.

The transform of the constant sheaf is computed from the stalk formula
(`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`) and
`H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs `Λ` finite with exponent invertible on `S`. The
transform of the skyscraper is compact-support base change of `Rp₂,!` along the zero section.
The comparison of the transforms for `ψ` and `ψ⁻¹` is base change of `Rp₂,!` along the
isomorphism `ι × 1`; it compares the chosen compactifications of `p₂` and of its conjugate by
`ι × 1`.

TODO: upgrade these back to `Iso` constructions once they can be built.

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

/-- The Fourier–Deligne transform of the skyscraper at the origin of `𝔸(n; S)` is the
constant sheaf, shifted by the relative dimension `r = #n`:

`FT_ψ(δ₀) ≅ Λ[r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(δ₀) ≅ Λ[1]`. Unlike
`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit` this holds for every
character: the kernel restricted to `{0} ×_S 𝔸(n; S)` is the Artin–Schreier sheaf of the zero
function.

Class: torsion; decided by compact-support base change of `Rp₂,!` along the zero section,
which needs `[Finite Λ]`.
(sketch blueprint: `sk-prop-first-formula`) -/
theorem nonempty_iso_affineFourierTransform_skyscraperZero [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (skyscraperZero Λ n S) ≅
        (shiftFunctor _ (Fintype.card n : ℤ)).obj (𝟙_ _)) :=
  sorry

/-- The Fourier–Deligne transform for the inverse character is the transform of the reflected
input, `ι = AlgebraicGeometry.AffineSpace.neg` being `x ↦ -x`:

`FT_{ψ⁻¹}(K) ≅ FT_ψ(ι^* K)`,

naturally in `K`:

```
                 ι^*
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
        FT_ψ⁻¹  ╲           │ FT_ψ
                  ▶         ▼
                    D(𝔸(n; S))
```

The kernel of `FT_{ψ⁻¹}` is the pullback of the kernel of `FT_ψ` along `ι × 1`, by
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv` and `b(-x, ξ) = -b(x, ξ)`.
It holds for every character.

Class: compactification-dependent; decided by independence of the compactification. The
blueprint proof is formal (base change along the isomorphism `ι × 1`); `[Finite Λ]` enters
solely through independence of the compactification
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), comparing the chosen compactifications
of `p₂` and of its conjugate by `ι × 1`.
(sketch blueprint: `sk-def-ft`, remark; `lem-fd-as-lisse`) -/
theorem nonempty_iso_affineFourierTransform_inv [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty (affineFourierTransform Λ n S Ψ⁻¹ ≅
        D((neg n S)^*[ModuleCat.{u + 1} Λ]) ⋙ affineFourierTransform Λ n S Ψ) :=
  sorry

end AlgebraicGeometry.Etale
