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

The *Fourier integrand* `ℱ_ψ(K) = p₁₃,*(p₁₂^* K ⊗ᴸ 𝒦_ψ)` on the triple product is the same
expression read with the ordinary direct image; it is not needed for any statement of this
block and is not formalised.

## Main definitions

- `AlgebraicGeometry.Etale.kernelTransform`: the kernel transform `Φ_𝒦` with shift `a`.
- `AlgebraicGeometry.Etale.fourierKernel`: the Fourier kernel `𝒦_ψ`.
- `AlgebraicGeometry.Etale.fourierTransform`: the Fourier–Deligne transform `FT_ψ`.
- `AlgebraicGeometry.Etale.fourierTransformBoundedConstructible`: the transform as a
  functor `Dᵇc(V, Λ) ⥤ Dᵇc(V', Λ)`.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`:
  the transform preserves the bounded constructible derived category.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

Two clauses of `sk-prop-kernel-lisse` and `sk-prop-well-defined` are deferred. That the
kernel is of *finite Tor amplitude* cannot be stated yet: the repository has no notion of
Tor amplitude for an object of `D(X_ét)`. That the transform is *triangulated* likewise
needs `Functor.CommShift` instances for the derived pullback, the derived tensor product
and `Rf_!`, none of which is available; the prose below records why it is expected to hold
rather than asserting it as a Lean statement.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

/-- The *kernel transform* `Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]` attached to a kernel
`𝒦 ∈ D((V ×_S V')_ét)` and a shift `a : ℤ`:

```
              V ×ₛ V'
             ╱       ╲
          p₁╱         ╲p₂
           ▼           ▼
           V            V'
            ╲          ╱
            π╲        ╱π'
              ▼      ▼
                 S
```

`K` is pulled back along `p₁`, tensored with `𝒦`, pushed forward with compact support
along `p₂` and shifted by `a`.

The Fourier–Deligne transform `AlgebraicGeometry.Etale.fourierTransform` is the kernel
transform of the Fourier kernel with shift the relative dimension. -/
noncomputable def kernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  D((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
    derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π') 𝒦 ⋙
      R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ a

/-- For a pairing `b ∈ Γ(V ×_S V', 𝒪)` between two `S`-schemes, the *Fourier kernel* `𝒦_ψ`
is the Artin–Schreier sheaf `ℒ_{Ψ, b} = b^* ℒ_Ψ` of the pairing, the pullback of the
Artin–Schreier sheaf of `𝔸¹` along `b : V ×_S V' ⟶ 𝔸¹`. On the affine line over a field, with
`V = V' = 𝔸¹` and the pairing the product `x ξ`, this is the sheaf usually written
`ℒ_{ψ(xξ)}`.

Being an Artin–Schreier sheaf, it is lisse of rank one
(`AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheafOf`) and multiplicative in
the character (`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_mul`), with
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_inv` identifying `𝒦_ψ⁻¹` with
`𝒦_{ψ⁻¹}`.
(sketch blueprint: `sk-def-kernel`, `sk-prop-kernel-lisse`) -/
noncomputable def fourierKernel [CharP Γ(pullback π π', ⊤) p] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  artinSchreierSheafZMod (pullback π π') Ψ b

/-- For a pairing `b ∈ Γ(V ×_S V', 𝒪)` between two `S`-schemes and a relative dimension `r`,
the *Fourier–Deligne transform* is

`FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦_ψ)[r]`,

the kernel transform of the Fourier kernel `𝒦_ψ` with shift `r`. The shift is part of the
definition: it is Laumon's normalization, for which the inversion theorem holds up to the
Tate twist `(-r)` and no further shift. The transform attached to the inverse character is
the same construction with `Ψ⁻¹` in place of `Ψ`; its kernel is the inverse of `𝒦_ψ` by
`AlgebraicGeometry.Etale.artinSchreierSheafInvIso`.
(sketch blueprint: `sk-def-ft`) -/
noncomputable def fourierTransform [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  kernelTransform Λ π π'
    ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) r

section BoundedConstructible

variable [CharP Γ(pullback π π', ⊤) p] [HasCompactification (pullback.snd π π')]
  [IsNoetherian V'] [LocallyOfFiniteType (pullback.snd π π')]
  [QuasiCompact (pullback.snd π π')]

/-- The Fourier–Deligne transform sends the bounded constructible derived category
`Dᵇc(V, Λ)` into `Dᵇc(V', Λ)`. Of its four factors only `Rp₂,!` is at issue: the pullback
`p₁^*`, the tensor product with the lisse rank-one kernel and the shift preserve bounded
constructibility for formal reasons, while `Rp₂,!` does so by Deligne's finiteness theorem,
which is why `p₂` is assumed of finite type over a noetherian target and `p` is assumed
invertible in `Λ`.
(sketch blueprint: `sk-prop-well-defined`) -/
theorem boundedConstructible_fourierTransform_obj_of_boundedConstructible
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V'
      ((fourierTransform Λ π π' Ψ b r).obj K) :=
  sorry

/-- The Fourier–Deligne transform as a functor `Dᵇc(V, Λ) ⥤ Dᵇc(V', Λ)`, the functor whose
existence `sk-prop-well-defined` asserts. It is exact and triangulated, each of the four
factors of `AlgebraicGeometry.Etale.kernelTransform` being triangulated; that is not
recorded as an instance here, see the module docstring.
(sketch blueprint: `sk-prop-well-defined`) -/
noncomputable def fourierTransformBoundedConstructible (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Dᵇc(V, ModuleCat.{u + 1} Λ) ⥤ Dᵇc(V', ModuleCat.{u + 1} Λ) :=
  ObjectProperty.lift _
    (Etale.DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) V ⋙
      fourierTransform Λ π π' Ψ b r)
    fun K ↦ boundedConstructible_fourierTransform_obj_of_boundedConstructible Λ π π' Ψ b r
      K.obj K.property

end BoundedConstructible

end AlgebraicGeometry.Etale
