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

- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`: composition of kernel
  transforms.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`: the kernel transform of a
  kernel supported on the diagonal is a tensor product.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution`: the convolution of the two
  Fourier kernels is the delta kernel.
- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv` and
  `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_self`: the inversion
  theorem, proved from the statements above.

## Implementation notes

The statements only assert that an isomorphism *exists*. Showing that `FT_ψ` is an
equivalence with inverse `FT_{ψ⁻¹}(r)`, or that the composition of kernel transforms is
compatible with the associativity of convolution, will need specific, coherent isomorphisms,
which `Classical.choice` cannot provide.

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
theorem nonempty_iso_kernelTransform_comp
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a c : ℤ) :
    Nonempty (kernelTransform Λ π π' 𝒦 a ⋙ kernelTransform Λ π' π'' 𝒦' c ≅
        kernelTransform Λ π π'' (kernelConvolution Λ π π' π'' 𝒦 𝒦') (a + c)) :=
  sorry

/-- Shifting the kernel shifts the kernel transform: the kernel transform of `𝒦[a]` with shift
`c` is the kernel transform of `𝒦` with shift `a + c`. This is formal, each factor of
`AlgebraicGeometry.Etale.kernelTransform` commuting with shifts. -/
theorem nonempty_iso_kernelTransform_shift [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a c : ℤ) :
    Nonempty (kernelTransform Λ π π' ((shiftFunctor _ a).obj 𝒦) c ≅
        kernelTransform Λ π π' 𝒦 (a + c)) :=
  sorry

/-- The kernel transform of a kernel `Δ_* N` supported on the diagonal of `V ×_S V`, with
shift `0`, is tensoring with `N`:

`Rp₂,!(p₁^* K ⊗ᴸ Δ_* N) ≅ K ⊗ᴸ N`,

naturally in `K`. For `N = Λ` this says that `Δ_* Λ` is the identity kernel. The proof is
the projection formula for the closed immersion `Δ`, which identifies the left side with
`Rp₂,! Δ_*(Δ^* p₁^* K ⊗ᴸ N)`, followed by `Δ_* = Δ_!` and `p₂ ∘ Δ = 𝟙`; `π` is separated so
that `Δ` is a closed immersion. -/
theorem nonempty_iso_kernelTransform_diagonal [IsSeparated π]
    [HasCompactification (pullback.snd π π)]
    (N : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (kernelTransform Λ π π
          ((R((pullback.diagonal π)_*[ModuleCat.{u + 1} Λ])).obj N) 0 ≅
        derivedTensorRight (ModuleCat.{u + 1} Λ) V N) :=
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
dimension. The companion statement `𝒦_ψ ∗ 𝒦_ψ ≅ (id × ι')_* Δ_* Λ(-r)[-2r]` is not stated:
its consequence `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_self` is
deduced from this one and `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`.

The computation uses `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, so the coefficients are torsion with
exponent invertible on `S`. The character must be **nontrivial** in the strong sense that
`Ψ 1 - 1` is a unit of `Λ`, which is what makes `H_c^*(𝔸¹, ℒ_ψ)` vanish: for `Ψ = 1` both
kernels are constant and the convolution is `Λ(-r)[-2r]`, supported everywhere, and `Ψ ≠ 1`
is not enough when `Λ` is not a domain
(see `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit`).
(sketch blueprint: `sk-prop-convolution-kernel`) -/
theorem nonempty_iso_fourierKernel_convolution [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (kernelConvolution Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S))) ≅
        (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj
          ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
            (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))))) :=
  sorry

/-- **Fourier inversion.** On `𝔸(n; S)` the Fourier–Deligne transform for the inverse
character inverts the Fourier–Deligne transform up to the Tate twist `(-r)`,
`r = #n` being the relative dimension:

`FT_{ψ⁻¹} FT_ψ(K) ≅ K(-r)`,

functorially in `K`:

```
                 FT_ψ
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
          (-r)  ╲           │ FT_ψ⁻¹
                  ▶         ▼
                    D(𝔸(n; S))
```

The proof composes the two kernel transforms
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`), computes the convolution of the
kernels (`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution`), moves the shift
out of the kernel and recognises the kernel transform of `Δ_* Λ(-r)` as the Tate twist
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`). The hypotheses are those
of the convolution computation: for `Ψ = 1` the transform is `Rp₂,! p₁^*(-)[r]`, which is not
invertible.
(sketch blueprint: `sk-thm-inversion`) -/
theorem nonempty_iso_affineFourierTransform_comp_inv [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (affineFourierTransform Λ n S Ψ ⋙ affineFourierTransform Λ n S Ψ⁻¹ ≅
        tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))) := by
  -- The kernel transform depends functorially on the kernel. Tensoring is first mapped over
  -- an arbitrary scheme `X`: doing so directly over the fibre product times out in the kernel.
  have ht {X : Scheme.{u}} {N N' : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (f : N ≅ N') :
      derivedTensorRight (ModuleCat.{u + 1} Λ) X N ≅
        derivedTensorRight (ModuleCat.{u + 1} Λ) X N' :=
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso f
  have hk {𝒦 𝒦' : DerivedCategory (Sheaf (pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (e : 𝒦 ≅ 𝒦') (a : ℤ) :
      kernelTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) 𝒦 a ≅
        kernelTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) 𝒦' a :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (ht e) _)
  obtain ⟨e₁⟩ := nonempty_iso_kernelTransform_comp Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
    (𝔸(n; S) ↘ S) ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))
    ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S)))
    (Fintype.card n) (Fintype.card n)
  obtain ⟨e₂⟩ := nonempty_iso_fourierKernel_convolution Λ n S Ψ hΨ
  obtain ⟨e₃⟩ := nonempty_iso_kernelTransform_shift Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
    ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
      (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))))
    (-2 * (Fintype.card n : ℤ)) (Fintype.card n + Fintype.card n)
  obtain ⟨e₄⟩ := nonempty_iso_kernelTransform_diagonal Λ (𝔸(n; S) ↘ S)
    (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ)))
  have hr : -2 * (Fintype.card n : ℤ) + (Fintype.card n + Fintype.card n) = 0 := by ring
  exact ⟨e₁ ≪≫ hk e₂ _ ≪≫ e₃ ≪≫ eqToIso (congrArg (kernelTransform Λ _ _ _) hr) ≪≫ e₄⟩

/-- Applying the Fourier–Deligne transform twice with the *same* character gives back the
reflection `ι^* K` of the input, Tate twisted by `(-r)`:

`FT_ψ FT_ψ(K) ≅ ι^* K(-r)`,

functorially in `K`, where `ι = AlgebraicGeometry.AffineSpace.neg` is `x ↦ -x`:

```
                 FT_ψ
     D(𝔸(n; S)) ─────▶ D(𝔸(n; S))
              ╲             │
     ι^* ⋙ (-r) ╲           │ FT_ψ
                  ▶         ▼
                    D(𝔸(n; S))
```

It follows from `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_inv`, which
gives `FT_ψ ≅ ι^* ⋙ FT_{ψ⁻¹}`, and inversion
(`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv`) for `ψ⁻¹`; the
hypotheses are those of inversion.
(sketch blueprint: `sk-thm-inversion`) -/
theorem nonempty_iso_affineFourierTransform_comp_self [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty (affineFourierTransform Λ n S Ψ ⋙ affineFourierTransform Λ n S Ψ ≅
        D((neg n S)^*[ModuleCat.{u + 1} Λ]) ⋙
          tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))) := by
  have h : Ψ⁻¹ 1 * Ψ 1 = 1 := by
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hΨ' : IsUnit (Ψ⁻¹ 1 - 1) := by
    rw [show Ψ⁻¹ 1 - 1 = -Ψ⁻¹ 1 * (Ψ 1 - 1) by linear_combination h]
    exact (IsUnit.of_mul_eq_one _ h).neg.mul hΨ
  obtain ⟨s⟩ := nonempty_iso_affineFourierTransform_inv Λ n S Ψ⁻¹
  obtain ⟨i⟩ := nonempty_iso_affineFourierTransform_comp_inv Λ n S Ψ⁻¹ hΨ'
  rw [inv_inv] at s i
  exact ⟨Functor.isoWhiskerRight s _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ i⟩

end Inversion

end AlgebraicGeometry.Etale
