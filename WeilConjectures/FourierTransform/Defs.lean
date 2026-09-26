/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!

# The Fourier–Deligne transform

Let `π : V ⟶ S` and `π' : V' ⟶ S` be two `S`-schemes — in the intended application a vector
bundle of rank `r` and its dual — and let `b ∈ Γ(V ×_S V', 𝒪)` be a pairing between them.
The *Fourier kernel* is the Artin–Schreier sheaf `𝒦_ψ = ℒ_{Ψ, b}` of the pairing, and the
*Fourier–Deligne transform* of `K ∈ D(V_ét)` is

`FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦_ψ)[r]`,

`p₁, p₂` being the two projections of `V ×_S V'`. The shift by the relative dimension `r`
is Laumon's normalization, the one for which the inversion theorem holds without a further
shift, up to the Tate twist `(-r)`.

The transform is a special case of a *kernel transform*
`Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]` attached to an arbitrary kernel `𝒦` on `V ×_S V'` and an
arbitrary shift `a`; kernel transforms are what the composition law used in the proof of
the inversion theorem is about, so they are introduced here once and for all.

## Main definitions

- `AlgebraicGeometry.Etale.kernelTransform`: the kernel transform `Φ_𝒦` with shift `a`.
- `AlgebraicGeometry.Etale.fourierKernel`: the Fourier kernel `𝒦_ψ`.
- `AlgebraicGeometry.Etale.fourierTransform`: the Fourier–Deligne transform `FT_ψ`.

## Main statements

- `AlgebraicGeometry.Etale.fourierKernelMul`: the Fourier kernel is multiplicative in the
  character, `𝒦_ψ ⊗ 𝒦_{ψ'} ≅ 𝒦_{ψψ'}`.
- `AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj`: the transform
  preserves the bounded constructible derived category.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

/-- Tensoring with a complex pulled back from the base along `f : X ⟶ Y`:
`K ↦ K ⊗ᴸ f^* N`. -/
noncomputable def tensorPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).flip.obj ((D((f)^*[ModuleCat.{u + 1} Λ])).obj N)

/-- Twisting by the Artin–Schreier sheaf of a global function: `K ↦ K ⊗ᴸ ℒ_{Ψ, f}`. -/
noncomputable def artinSchreierTwist (X : Scheme.{u}) [CharP Γ(X, ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).flip.obj
    ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheaf X Ψ f))

/-- The *kernel transform* `Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]` attached to a kernel
`𝒦 ∈ D((V ×_S V')_ét)` and a shift `a : ℤ`, where `p₁ : V ×_S V' ⟶ V` and
`p₂ : V ×_S V' ⟶ V'` are the two projections.

The Fourier–Deligne transform `AlgebraicGeometry.Etale.fourierTransform` is the kernel
transform of the Fourier kernel with shift the relative dimension. -/
noncomputable def kernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  D((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
    (-⊗ᴸ-(pullback π π')[ModuleCat.{u + 1} Λ]).flip.obj 𝒦 ⋙
      R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ a

/-- Blueprint `sk-def-kernel`: The Fourier kernel and integrand.

For a pairing `b ∈ Γ(V ×_S V', 𝒪)` between two `S`-schemes, the *Fourier kernel* `𝒦_ψ` is
the Artin–Schreier sheaf `ℒ_{Ψ, b}` of the pairing. On the affine line over a field, with
`V = V' = 𝔸¹` and the pairing the product `x ξ`, this is the sheaf usually written
`ℒ_{ψ(xξ)}`.

The *Fourier integrand* `ℱ_ψ(K) = p₁₃,*(p₁₂^* K ⊗ᴸ 𝒦_ψ)` on the triple product is the
same expression read with the ordinary direct image; it is not needed for the statements
of this file. -/
noncomputable def fourierKernel [CharP Γ(pullback π π', ⊤) p] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  artinSchreierSheaf (pullback π π') Ψ b

/-- Blueprint `sk-prop-kernel-lisse`: P1: the kernel is a lisse rank-one character sheaf.

The Fourier kernel is multiplicative in the character, `𝒦_ψ ⊗ 𝒦_{ψ'} ≅ 𝒦_{ψψ'}`; taking
`ψ' = ψ⁻¹` gives `𝒦_ψ⁻¹ ≅ 𝒦_{ψ⁻¹}`. That the kernel is lisse of rank one is
`AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf` together with
`AlgebraicGeometry.Etale.artinSchreierSheafZero`, since the kernel is by definition an
Artin–Schreier sheaf; being lisse of rank one, it is in particular of finite Tor
amplitude. -/
noncomputable def fourierKernelMul [CharP Γ(pullback π π', ⊤) p] (Ψ Ψ' : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    fourierKernel Λ π π' Ψ b ⊗ fourierKernel Λ π π' Ψ' b ≅ fourierKernel Λ π π' (Ψ * Ψ') b :=
  sorry

/-- Blueprint `sk-def-ft`: The Fourier–Deligne transform.

For a pairing `b ∈ Γ(V ×_S V', 𝒪)` between two `S`-schemes and a relative dimension `r`,
the Fourier–Deligne transform is

`FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦_ψ)[r]`,

the kernel transform of the Fourier kernel `𝒦_ψ` with shift `r`. The shift is part of the
definition: it is Laumon's normalization, for which the inversion theorem holds up to the
Tate twist `(-r)` and no further shift. The transform attached to the inverse character is
the same construction with `Ψ⁻¹` in place of `Ψ`; its kernel is the inverse of `𝒦_ψ` by
`AlgebraicGeometry.Etale.fourierKernelMul`. -/
noncomputable def fourierTransform [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  kernelTransform Λ π π'
    ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) r

/-- Blueprint `sk-prop-well-defined`: P2: the transform is an exact triangulated functor.

The Fourier–Deligne transform sends the bounded constructible derived category `Dᵇc(V, Λ)`
into `Dᵇc(V', Λ)`. That it is exact and triangulated is automatic: each of its four
factors — the pullback `p₁^*`, the derived tensor product with a fixed object, the derived
direct image with compact support `Rp₂,!` and the shift — is a triangulated functor. -/
theorem boundedConstructible_fourierTransform_obj [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V'
      ((fourierTransform Λ π π' Ψ b r).obj K) :=
  sorry

end AlgebraicGeometry.Etale
