/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierInversion.Vanishing

/-!
# Fourier inversion: the composite of two Fourier transforms

`FT_{ψ⁻¹} ∘ FT_ψ` computed on the triple product `𝔸³` (blueprint `lem-fd-kernel-composition`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **`FT_{ψ⁻¹} ∘ FT_ψ` on the triple product** (blueprint `lem-fd-kernel-composition`,
`sk-lem-kernel-composition`, without forming the convolution kernel). On `𝔸³` with points
`(x, ξ, y)`,

`FT_{ψ⁻¹} FT_ψ (K) ≅ Rr₃₀!(ℒ_ψ((x - y) ξ) ⊗ r₁^* K)[1][1]`

naturally in `K`, with `r₁ = r₁₃ ≫ pr₁` and `r₃ = r₁₃ ≫ pr₂`. It follows from compact-support
base change along `pr₁ : (ξ, y) ↦ ξ`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_upperStar`), the projection
formula for `r₂₃` and the composition `R(r₂₃ ≫ pr₂)₀! ≅ Rpr₂₀! Rr₂₃₀!`, together with
`ℒ_ψ(x ξ) ⊗ ℒ_{ψ⁻¹}(ξ y) ≅ ℒ_ψ((x - y) ξ)` (blueprint `lem-fd-as-lisse`). -/
theorem nonempty_iso_fourierTransform_comp_fourierTransform_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (fourierTransform (l := l) ψ ⋙ fourierTransform ψ⁻¹ ≅
      WeilComplex.upperStar (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀) ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ
          ((affineTripleProduct.proj₁₃ k₀).appTop
              ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop
                (AffineSpace.coord _ PUnit.unit)) *
            (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
              (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀) ⋙
        shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)) :=
  sorry


end AlgebraicGeometry
