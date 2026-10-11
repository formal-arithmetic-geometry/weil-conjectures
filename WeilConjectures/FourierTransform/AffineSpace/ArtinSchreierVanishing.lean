/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace
public import WeilConjectures.FourierTransform.ArtinSchreier

/-!
# Compactly supported cohomology of the affine line with Artin–Schreier coefficients

Let `T` be a scheme of characteristic `p` and `Ψ` an additive character of `𝔽_p` with values
in a finite coefficient ring `Λ` in which `p` and the exponent of `Λ` are invertible on `T`, and
such that `Ψ(1) - 1` is a unit. Then the compactly supported cohomology of the relative affine
line `π : 𝔸¹_T ⟶ T` with coefficients in the Artin–Schreier sheaf `ℒ_{Ψ, x}` of the
coordinate vanishes: `Rπ_! ℒ_{Ψ, x} = 0`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_coord`:
  `Rπ_! ℒ_{Ψ, x} = 0`.

## Blueprint

This is the vanishing `H^*_c(𝔸¹, ℒ_ψ) = 0` used in the proofs of `sk-prop-first-formula` and
`sk-prop-convolution-kernel` (blueprint `lem-fd-first-formula`, `lem-fd-convolution-kernel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]

/-- **Vanishing of the compactly supported cohomology of `ℒ_ψ` on the affine line.** For a
scheme `T` of characteristic `p`, a finite coefficient ring `Λ` whose exponent is invertible on
`T`, and an additive character `Ψ` of `𝔽_p` with `Ψ(1) - 1` a unit of `Λ`, the compactly
supported direct image of the Artin–Schreier sheaf `ℒ_{Ψ, x}` of the coordinate along
`π : 𝔸¹_T ⟶ T` vanishes.
(sketch blueprint: `sk-prop-first-formula`, proof) -/
theorem isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_coord [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] (T : Scheme.{u}) [HasInvertibleExponent Λ T]
    [CharP Γ(𝔸(PUnit.{u + 1}; T), ⊤) p] (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    IsZero ((R(𝔸(PUnit.{u + 1}; T) ↘ T)_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafZMod 𝔸(PUnit.{u + 1}; T) Ψ (AffineSpace.coord T PUnit.unit)))) :=
  sorry

end AlgebraicGeometry.Etale
