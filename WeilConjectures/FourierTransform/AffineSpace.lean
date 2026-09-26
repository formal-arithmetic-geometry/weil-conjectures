/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.SixFunctors.Etale.TateTwist

/-!

# The Fourier–Deligne transform on affine space

The Fourier–Deligne transform of `WeilConjectures.FourierTransform.Defs` is stated for an
arbitrary pair of `S`-schemes with a pairing. Its main case is affine `n`-space `𝔸(n; S)`
paired with itself by the standard pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative
dimension `#n`; this file records that datum and the computation of the transform of the
two simplest complexes on the affine line, the unit and the skyscraper at the origin.

## Main definitions

- `AlgebraicGeometry.AffineSpace.stdPairing`: the standard pairing on `𝔸(n; S) ×_S 𝔸(n; S)`.
- `AlgebraicGeometry.AffineSpace.line`: the affine line `𝔸¹_S`.
- `AlgebraicGeometry.AffineSpace.neg`: the reflection `x ↦ -x` of `𝔸(n; S)`.
- `AlgebraicGeometry.AffineSpace.zeroSection`: the zero section `S ⟶ 𝔸(n; S)`.
- `AlgebraicGeometry.Etale.affineFourierTransform`: the Fourier–Deligne transform of
  `𝔸(n; S)` with the standard pairing.
- `AlgebraicGeometry.Etale.skyscraperZero`: the skyscraper `δ₀` at the origin.

## Main statements

- `AlgebraicGeometry.Etale.fourierTransformUnitIso` and
  `AlgebraicGeometry.Etale.fourierTransformSkyscraperZeroIso`: on the affine line the
  transform exchanges the unit and the skyscraper at the origin.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace AffineSpace

variable (n : Type u) [Fintype n] (S : Scheme.{u})

/-- The standard pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` on `𝔸(n; S) ×_S 𝔸(n; S)`, a global function on
the product. -/
noncomputable def stdPairing : Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) :=
  ∑ i : n, (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).appTop (coord S i) *
    (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).appTop (coord S i)

/-- The affine line `𝔸¹_S` over `S`. -/
noncomputable abbrev line : Scheme.{u} := 𝔸(PUnit.{u + 1}; S)

/-- The reflection `x ↦ -x` of `𝔸(n; S)`, the inverse of the group law. -/
noncomputable def neg : 𝔸(n; S) ⟶ 𝔸(n; S) :=
  homOfVector (𝔸(n; S) ↘ S) fun i ↦ -coord S i

/-- The zero section `S ⟶ 𝔸(n; S)`, the unit of the group law. -/
noncomputable def zeroSection : S ⟶ 𝔸(n; S) :=
  homOfVector (𝟙 S) 0

/-- The diagonal `𝔸(n; S) ⟶ 𝔸(n; S) ×_S 𝔸(n; S)`. -/
noncomputable def diagonal : 𝔸(n; S) ⟶ pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

end AffineSpace

namespace Etale

open AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime]
variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The Fourier–Deligne transform of affine `n`-space over `S`: the transform of
`AlgebraicGeometry.Etale.fourierTransform` for `𝔸(n; S)` paired with itself by the standard
pairing and shifted by the relative dimension `#n`. On the affine line this is
`FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ ℒ_{ψ(xξ)})[1]`. -/
noncomputable def affineFourierTransform (Ψ : AddChar (ZMod p) Λ) :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fourierTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S) (Fintype.card n)

/-- The unit complex `Λ` on `𝔸(n; S)`: the constant sheaf with value `Λ`, placed in
degree `0`. -/
noncomputable def unitComplex (X : Scheme.{u}) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)

/-- The skyscraper `δ₀` at the origin of `𝔸(n; S)`: the direct image of the unit complex
along the zero section, placed in degree `0`. -/
noncomputable def skyscraperZero :
    DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj (unitComplex Λ S)

/-- Blueprint `sk-prop-first-formula`: P4: the constant sheaf and the skyscraper are
exchanged.

On the affine line the Fourier–Deligne transform sends the constant sheaf to the skyscraper
at the origin of the dual line, Tate twisted and shifted: `FT_ψ(Λ) ≅ δ₀(-1)[-1]`. -/
noncomputable def fourierTransformUnitIso (Ψ : AddChar (ZMod p) Λ) :
    (affineFourierTransform Λ n S Ψ).obj (unitComplex Λ (𝔸(n; S))) ≅
      (shiftFunctor _ (-(Fintype.card n : ℤ))).obj
        ((tateTwist (ModuleCat.{u + 1} Λ) (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj
          (skyscraperZero Λ n S)) :=
  sorry

/-- Blueprint `sk-prop-first-formula`: P4: the constant sheaf and the skyscraper are
exchanged.

On the affine line the Fourier–Deligne transform sends the skyscraper at the origin to the
constant sheaf, shifted: `FT_ψ(δ₀) ≅ Λ[1]`. -/
noncomputable def fourierTransformSkyscraperZeroIso (Ψ : AddChar (ZMod p) Λ) :
    (affineFourierTransform Λ n S Ψ).obj (skyscraperZero Λ n S) ≅
      (shiftFunctor _ (Fintype.card n : ℤ)).obj (unitComplex Λ (𝔸(n; S))) :=
  sorry

end Etale

end AlgebraicGeometry
