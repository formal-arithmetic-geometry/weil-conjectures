/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.AffineSpace

/-!

# Invertibility of the Fourier–Deligne transform

Kernel transforms compose: the composite of the kernel transforms of `𝒦` and `𝒦'` is the
kernel transform of the convolution `𝒦' ∗ 𝒦`, with the shifts added. Applied to the Fourier
kernels this reduces the inversion theorem to a single computation, that the convolution of
`𝒦_{ψ⁻¹}` with `𝒦_ψ` is the delta kernel `Δ_* Λ(-r)[-2r]`.

## Main definitions

- `AlgebraicGeometry.Etale.tripleProj₁₃`: the projection
  `V ×_S V' ×_S V'' ⟶ V ×_S V''`.
- `AlgebraicGeometry.Etale.kernelConvolution`: the convolution
  `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`.

## Main statements

- `AlgebraicGeometry.Etale.kernelTransformCompIso`: composition of kernel transforms.
- `AlgebraicGeometry.Etale.fourierKernelConvolutionIso`: the convolution of the two Fourier
  kernels is the delta kernel.
- `AlgebraicGeometry.Etale.fourierTransformInversionIso` and
  `AlgebraicGeometry.Etale.fourierTransformSquareIso`: the inversion theorem.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime]

section Convolution

variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The projection `r₁₃ : V ×_S V' ×_S V'' ⟶ V ×_S V''` of the triple product, the latter
realised as `(V ×_S V') ×_{V'} (V' ×_S V'')`; the two other projections `r₁₂` and `r₂₃` are
the two projections of that fibre product. -/
noncomputable def tripleProj₁₃ :
    pullback (pullback.snd π π') (pullback.fst π' π'') ⟶ pullback π π'' :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst π π')
    (pullback.snd _ _ ≫ pullback.snd π' π'') (by
      have h₁ : pullback.fst π π' ≫ π = pullback.snd π π' ≫ π' := pullback.condition
      have h₂ : pullback.fst π' π'' ≫ π' = pullback.snd π' π'' ≫ π'' := pullback.condition
      have h₃ : pullback.fst (pullback.snd π π') (pullback.fst π' π'') ≫ pullback.snd π π' =
          pullback.snd (pullback.snd π π') (pullback.fst π' π'') ≫ pullback.fst π' π'' :=
        pullback.condition
      rw [Category.assoc, h₁, ← Category.assoc, h₃, Category.assoc, h₂, Category.assoc])

/-- The convolution `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')` of a kernel `𝒦` on `V ×_S V'`
with a kernel `𝒦'` on `V' ×_S V''`, a kernel on `V ×_S V''`. -/
noncomputable def kernelConvolution [HasCompactification (tripleProj₁₃ π π' π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (Sheaf (pullback π π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (R(tripleProj₁₃ π π' π'')_![ModuleCat.{u + 1} Λ]).obj
    (((-⊗ᴸ-(pullback (pullback.snd π π') (pullback.fst π' π''))[ModuleCat.{u + 1} Λ]).obj
        ((D((pullback.fst (pullback.snd π π')
          (pullback.fst π' π''))^*[ModuleCat.{u + 1} Λ])).obj 𝒦)).obj
      ((D((pullback.snd (pullback.snd π π')
        (pullback.fst π' π''))^*[ModuleCat.{u + 1} Λ])).obj 𝒦'))

/-- Blueprint `sk-lem-kernel-composition`: P11: composition of kernel transforms.

The composite of the kernel transform of `𝒦` with shift `a` and the kernel transform of
`𝒦'` with shift `c` is the kernel transform of the convolution `𝒦' ∗ 𝒦` with shift
`a + c`. In particular `FT_{ψ⁻¹} ∘ FT_ψ` is the kernel transform of
`𝒦_{ψ⁻¹} ∗ 𝒦_ψ` with shift `2r`. -/
noncomputable def kernelTransformCompIso [HasCompactification (tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a c : ℤ) :
    kernelTransform Λ π π' 𝒦 a ⋙ kernelTransform Λ π' π'' 𝒦' c ≅
      kernelTransform Λ π π'' (kernelConvolution Λ π π' π'' 𝒦 𝒦') (a + c) :=
  sorry

end Convolution

section AffineSpace

variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
variable [HasCompactification (tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- Blueprint `sk-prop-convolution-kernel`: P12: the convolution of the kernels is the delta
kernel.

Over a field, with `V = 𝔸ⁿ`, the convolution of the kernel of `FT_{ψ⁻¹}` with the kernel of
`FT_ψ` is the delta kernel `Δ_* Λ(-r)[-2r]` supported on the diagonal; here `Ψ'` is the
inverse character, `Ψ * Ψ' = 1`. The companion statement
`𝒦_ψ ∗ 𝒦_ψ ≅ (id × ι')_* Δ_* Λ(-r)[-2r]` is the same computation with `ψ` in place of
`ψ⁻¹`, and is recorded through its consequence
`AlgebraicGeometry.Etale.fourierTransformSquareIso`. -/
noncomputable def fourierKernelConvolutionIso (Ψ Ψ' : AddChar (ZMod p) Λ) (hΨ : Ψ * Ψ' = 1) :
    kernelConvolution Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ' (stdPairing n S))) ≅
      (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj
        ((tateTwist (ModuleCat.{u + 1} Λ) _ (-(Fintype.card n : ℤ))).obj
          ((R((diagonal n S)_*[ModuleCat.{u + 1} Λ])).obj (unitComplex Λ (𝔸(n; S))))) :=
  sorry

/-- Blueprint `sk-thm-inversion`: P13: invertibility of the transform.

Over a field, with `V = 𝔸ⁿ` of dimension `r`, the Fourier–Deligne transform for the inverse
character inverts the Fourier–Deligne transform up to the Tate twist `(-r)`:
`FT_{ψ⁻¹} FT_ψ(K) ≅ K(-r)`. -/
noncomputable def fourierTransformInversionIso (Ψ Ψ' : AddChar (ZMod p) Λ) (hΨ : Ψ * Ψ' = 1)
    (K : DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (affineFourierTransform Λ n S Ψ').obj ((affineFourierTransform Λ n S Ψ).obj K) ≅
      (tateTwist (ModuleCat.{u + 1} Λ) _ (-(Fintype.card n : ℤ))).obj K :=
  sorry

/-- Blueprint `sk-thm-inversion`: P13: invertibility of the transform.

Applying the Fourier–Deligne transform twice with the same character gives back the
reflection `ι'^* K` of the input, Tate twisted by `(-r)`:
`FT_ψ FT_ψ(K) ≅ ι'^* K(-r)`. -/
noncomputable def fourierTransformSquareIso (Ψ : AddChar (ZMod p) Λ)
    (K : DerivedCategory (Sheaf (𝔸(n; S)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (affineFourierTransform Λ n S Ψ).obj ((affineFourierTransform Λ n S Ψ).obj K) ≅
      (tateTwist (ModuleCat.{u + 1} Λ) _ (-(Fintype.card n : ℤ))).obj
        ((D((neg n S)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

end AffineSpace

end AlgebraicGeometry.Etale
