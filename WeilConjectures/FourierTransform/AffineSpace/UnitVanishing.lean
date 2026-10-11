/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing
public import WeilConjectures.FourierTransform.AffineSpace.Transform
public import WeilConjectures.FourierTransform.Properties.Stalk

/-!
# The transform of the constant sheaf vanishes off the origin

On relative affine space `𝔸(n; S)`, for a character `Ψ` with `Ψ(1) - 1` a unit, the
Fourier–Deligne transform of the constant sheaf vanishes on the complement of the zero section
of the dual. On the basic open set `ξᵢ ≠ 0` the linear form `x ↦ ⟨x, ξ⟩` is a coordinate
after a linear change of variables, so the restriction of the transform is the compactly
supported cohomology of `𝔸^{n-1}` times that of `ℒ_{ψ(t)}` on the affine line, which vanishes
(`AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_coord`).

## Main statements

- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_affineFourierTransform_unit`: the
  restriction of `FT_ψ(Λ)` to the complement of the zero section is zero.
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

/-- The Fourier–Deligne transform of the constant sheaf on `𝔸(n; S)` vanishes off the origin:
its restriction to the open complement `U` of the zero section of the dual is zero. The
character must satisfy `IsUnit (Ψ 1 - 1)`, which is what makes `H^*_c(𝔸¹, ℒ_ψ)` vanish.
(sketch blueprint: `sk-prop-first-formula`, proof) -/
theorem isZero_leftDerivedUpperStar_affineFourierTransform_unit [Finite Λ]
    [HasInvertibleExponent Λ S] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) {U : Scheme.{u}} (j : U ⟶ 𝔸(n; S))
    [IsOpenImmersion j] (hj : Set.range j.base = (Set.range (zeroSection n S).base)ᶜ) :
    IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj
      ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _))) :=
  sorry

end AlgebraicGeometry.Etale
