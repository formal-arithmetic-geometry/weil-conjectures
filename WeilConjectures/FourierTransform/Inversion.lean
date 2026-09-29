/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.AffineSpace
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!

# Invertibility of the Fourier–Deligne transform

Kernel transforms compose: the composite of the kernel transforms of `𝒦` and `𝒦'` is the
kernel transform of the convolution `𝒦' ∗ 𝒦`, with the shifts added. Applied to the Fourier
kernels this reduces the inversion theorem to a single computation, that the convolution of
`𝒦_{ψ⁻¹}` with `𝒦_ψ` is the delta kernel `Δ_* Λ(-r)[-2r]`.

## Main definitions

- `AlgebraicGeometry.Etale.kernelConvolution`: the convolution
  `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`.

## Main statements

- `AlgebraicGeometry.Etale.kernelTransformCompIso`: composition of kernel transforms.
- `AlgebraicGeometry.Etale.fourierKernelConvolutionIso`: the convolution of the two Fourier
  kernels is the delta kernel.
- `AlgebraicGeometry.Etale.fourierTransformInversionIso` and
  `AlgebraicGeometry.Etale.fourierTransformSquareIso`: the inversion theorem.

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

section Convolution

variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The convolution `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')` of a kernel `𝒦` on `V ×_S V'`
with a kernel `𝒦'` on `V' ×_S V''`, a kernel on `V ×_S V''`.

The triple product `V ×_S V' ×_S V''` is realised as `(V ×_S V') ×_{V'} (V' ×_S V'')`, whose
two projections are `r₁₂` and `r₂₃`; `r₁₃` is
`CategoryTheory.Limits.pullback.tripleProj₁₃`:

```
                       𝒦
    V ×ₛ V' ×ₛ V'' ──r₁₂──▶ V ×ₛ V'
           │ ╲
           │   ╲ r₁₃
        r₂₃│     ╲
           ▼       ▶ V ×ₛ V''
      V' ×ₛ V''
           𝒦'
```

`𝒦` is pulled back along `r₁₂`, `𝒦'` along `r₂₃`, the two are tensored, and the result is
pushed forward with compact support along `r₁₃`. -/
noncomputable def kernelConvolution
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (Sheaf (pullback π π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (R(pullback.tripleProj₁₃ π π' π'')_![ModuleCat.{u + 1} Λ]).obj
    ((derivedTensorRight (ModuleCat.{u + 1} Λ)
        (pullback (pullback.snd π π') (pullback.fst π' π''))
        ((D((pullback.snd (pullback.snd π π')
          (pullback.fst π' π''))^*[ModuleCat.{u + 1} Λ])).obj 𝒦')).obj
      ((D((pullback.fst (pullback.snd π π')
        (pullback.fst π' π''))^*[ModuleCat.{u + 1} Λ])).obj 𝒦))

/-- The composite of the kernel transform of `𝒦` with shift `a` and the kernel transform of
`𝒦'` with shift `c` is the kernel transform of the convolution `𝒦' ∗ 𝒦` with shift `a + c`.

The proof reads the composite on the triple product

```
                       𝒦
    V ×ₛ V' ×ₛ V'' ──r₁₂──▶ V ×ₛ V'
           │ ╲
           │   ╲ r₁₃
        r₂₃│     ╲
           ▼       ▶ V ×ₛ V''
      V' ×ₛ V''
           𝒦'
```

and applies base change to the cartesian square with sides `r₁₂`, `r₂₃`, `p₂` and `q₁`; the
compactifiability of `r₂₃` that this needs is the instance
`AlgebraicGeometry.HasCompactification.pullback_snd` applied to `p₂ = pullback.snd π π'`.

In particular `FT_{ψ⁻¹} ∘ FT_ψ` is the kernel transform of `𝒦_{ψ⁻¹} ∗ 𝒦_ψ` with shift `2r`.
(sketch blueprint: `sk-lem-kernel-composition`) -/
noncomputable def kernelTransformCompIso
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a c : ℤ) :
    kernelTransform Λ π π' 𝒦 a ⋙ kernelTransform Λ π' π'' 𝒦' c ≅
      kernelTransform Λ π π'' (kernelConvolution Λ π π' π'' 𝒦 𝒦') (a + c) :=
  sorry

end Convolution

section Inversion

variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
variable [HasCompactification
  (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The convolution of the kernel of `FT_{ψ⁻¹}` with the kernel of `FT_ψ` on `𝔸(n; S)` is
the delta kernel `Δ_* Λ(-r)[-2r]` supported on the diagonal, `r = #n` being the relative
dimension. The companion statement `𝒦_ψ ∗ 𝒦_ψ ≅ (id × ι')_* Δ_* Λ(-r)[-2r]` is the same
computation with `ψ` in place of `ψ⁻¹`, and is recorded through its consequence
`AlgebraicGeometry.Etale.fourierTransformSquareIso`.

The character must be **nontrivial**: for `Ψ = 1` both kernels are constant and the
convolution is `Λ(-r)[-2r]`, supported everywhere.
(sketch blueprint: `sk-prop-convolution-kernel`) -/
noncomputable def fourierKernelConvolutionIso [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : Ψ ≠ 1) :
    kernelConvolution Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S))) ≅
      (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj
        ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
          ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj
            (constantComplex Λ (𝔸(n; S))))) :=
  sorry

/-- **Fourier inversion.** On `𝔸(n; S)` the Fourier–Deligne transform for the inverse
character inverts the Fourier–Deligne transform up to the Tate twist `(-r)`,
`r = #n` being the relative dimension:

`FT_{ψ⁻¹} FT_ψ(K) ≅ K(-r)`,

functorially in `K`. The character must be **nontrivial**: for `Ψ = 1` the transform is
`Rp₂,! p₁^*(-)[r]`, which is not invertible.
(sketch blueprint: `sk-thm-inversion`) -/
noncomputable def fourierTransformInversionIso [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : Ψ ≠ 1) :
    affineFourierTransform Λ n S Ψ ⋙ affineFourierTransform Λ n S Ψ⁻¹ ≅
      tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ)) :=
  sorry

/-- Applying the Fourier–Deligne transform twice with the *same* character gives back the
reflection `ι'^* K` of the input, Tate twisted by `(-r)`:

`FT_ψ FT_ψ(K) ≅ ι'^* K(-r)`,

functorially in `K`, where `ι' = AlgebraicGeometry.AffineSpace.neg` is `x ↦ -x`. The
character must be **nontrivial**, for the same reason as in
`AlgebraicGeometry.Etale.fourierTransformInversionIso`.
(sketch blueprint: `sk-thm-inversion`) -/
noncomputable def fourierTransformSquareIso [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : Ψ ≠ 1) :
    affineFourierTransform Λ n S Ψ ⋙ affineFourierTransform Λ n S Ψ ≅
      D((neg n S)^*[ModuleCat.{u + 1} Λ]) ⋙
        tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ)) :=
  sorry

end Inversion

end AlgebraicGeometry.Etale
