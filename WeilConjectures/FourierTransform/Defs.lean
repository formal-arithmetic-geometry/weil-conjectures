/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform

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
arbitrary shift `a` (`WeilConjectures.SixFunctors.Etale.Derived.KernelTransform`).

The *Fourier integrand* `ℱ_ψ(K) = p₁₃,*(p₁₂^* K ⊗ᴸ 𝒦_ψ)` on the triple product is the same
expression read with the ordinary direct image; it is not needed for any statement of this
block and is not formalised.

## Main definitions

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

## Coefficients

The kernel transform is defined for any coefficient category `A` on which the étale six
functors are built. The Fourier kernel is a character sheaf: `Ψ : AddChar (ZMod p) Λ` acts on
it by scalars of a ring, so the Fourier kernel and the Fourier–Deligne transform are defined
over `ModuleCat Λ`, for any commutative ring `Λ` in which `p` is invertible.

The theorems of the Fourier transform files assume the coefficient hypotheses of the strongest
input of their proofs:

- **general**: formal six-functor manipulations (shifts, pullback along isomorphisms, the
  projection formula for a closed immersion, multiplicativity of Artin–Schreier sheaves): no
  hypothesis on the coefficients;
- **compactification-dependent**: the blueprint proof is formal, but `R(f)_!` is computed with
  a chosen compactification, and the proof compares two compactifications of a quasi-compact
  morphism (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`). That comparison rests on
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`, which is
  not proved and whose hypotheses are not settled: besides torsion coefficients, for proper
  base change, it needs a finiteness condition on the morphism giving finite cohomological
  dimension, to pass from `D⁺` to the unbounded derived category. These theorems assume
  `[Finite Λ]` and quasi-compactness of the morphism whose compactifications are compared;
- **torsion**: compact-support base change, the projection formula for `Rp₂,!`, Deligne
  finiteness of `Rf_!` or the cohomology of `𝔸^r`: `[Finite Λ] [HasInvertibleExponent Λ S]`,
  or `[Finite Λ]` alone where the blueprint proof does not use the exponent.

TODO: once the hypotheses of
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison` are fixed,
give the compactification-dependent theorems exactly those hypotheses.

In the blueprint the `ℚ̄_ℓ` versions are deduced from the torsion ones by reduction. That
deduction, and the `ℚ̄_ℓ` statements themselves, are not formalised here.

## Implementation notes

`AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`:
of the four factors of the transform only `Rp₂,!` is at issue. The pullback `p₁^*`, the tensor
product with the lisse rank-one kernel and the shift preserve bounded constructibility for
formal reasons, while `Rp₂,!` does so by the finiteness theorem
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`. That theorem is stated
over a base field `k`, for finite `Λ` whose exponent is invertible on the source; hence `V'` is
assumed locally of finite type over `k`, `p₂` of finite type, and the exponent invertible on
`S`, which gives it on `V ×_S V'` by `AlgebraicGeometry.HasInvertibleExponent.of_hom`.

TODO: neither restriction is needed for `Rf_!`. For torsion coefficients and `f` of finite
presentation, `Rf_!` preserves constructibility over any quasi-compact quasi-separated base,
with no invertibility of the exponent (SGA 4 XVII 5.3.6). Once
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek` is stated in that
generality, drop the field and `[HasInvertibleExponent Λ S]` here.

## Deferred clauses

Two clauses of `sk-prop-kernel-lisse` and `sk-prop-well-defined` are deferred. That the
kernel is of *finite Tor amplitude* cannot be stated yet: the repository has no notion of
Tor amplitude for an object of `D(X_ét)`. That the transform is *triangulated* is not recorded
either. Its factors commute with shifts (`Functor.CommShift` instances for `Rf_!`, `Lg^*` and
`(derivedTensor A X).flip.obj K` are in `WeilConjectures.SixFunctors.Etale.Derived.Shift`),
but triangulatedness of the derived tensor product and of `Rf_!` is not yet available.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

/-- For a pairing `b ∈ Γ(V ×_S V', 𝒪)` between two `S`-schemes, the *Fourier kernel* `𝒦_ψ`
is the Artin–Schreier sheaf `ℒ_{Ψ, b} = b^* ℒ_Ψ` of the pairing, the pullback of the
Artin–Schreier sheaf of `𝔸¹` along `b : V ×_S V' ⟶ 𝔸¹`. On the affine line over a field, with
`V = V' = 𝔸¹` and the pairing the product `x ξ`, this is the sheaf usually written
`ℒ_{ψ(xξ)}`.

Being an Artin–Schreier sheaf, it is lisse of rank one
(`AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheafOf`) and multiplicative in
the character (`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_mul`), with
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv` identifying `𝒦_ψ⁻¹` with
`𝒦_{ψ⁻¹}`. It is defined for every commutative ring `Λ` in which `p` is invertible.
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
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv`. Like the kernel, it is
defined for every commutative ring `Λ` in which `p` is invertible; torsion coefficients are
only assumed by the theorems that need them.
(sketch blueprint: `sk-def-ft`) -/
noncomputable def fourierTransform [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  kernelTransform (ModuleCat.{u + 1} Λ) π π'
    ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) r

section BoundedConstructible

variable [Finite Λ] [HasInvertibleExponent Λ S]
  [CharP Γ(pullback π π', ⊤) p] [HasCompactification (pullback.snd π π')]
  [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]

/-- For `V'` locally of finite type over a field `k`, the Fourier–Deligne transform sends the
bounded constructible derived category `Dᵇc(V, Λ)` into `Dᵇc(V', Λ)`.
(sketch blueprint: `sk-prop-well-defined`) -/
theorem boundedConstructible_fourierTransform_obj_of_boundedConstructible {k : Type u}
    [Field k] (aV' : V' ⟶ Spec (.of k)) [LocallyOfFiniteType aV'] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V'
      ((fourierTransform Λ π π' Ψ b r).obj K) :=
  sorry

/-- For `V'` locally of finite type over a field, the Fourier–Deligne transform as a functor
`Dᵇc(V, Λ) ⥤ Dᵇc(V', Λ)`, the functor whose existence `sk-prop-well-defined` asserts.
(sketch blueprint: `sk-prop-well-defined`) -/
noncomputable def fourierTransformBoundedConstructible
    (hV' : ∃ (k : Type u) (_ : Field k) (a : V' ⟶ Spec (.of k)), LocallyOfFiniteType a)
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Dᵇc(V, ModuleCat.{u + 1} Λ) ⥤ Dᵇc(V', ModuleCat.{u + 1} Λ) :=
  ObjectProperty.lift _
    (Etale.DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) V ⋙
      fourierTransform Λ π π' Ψ b r)
    fun K ↦ by
      obtain ⟨k, _, a, _⟩ := hV'
      exact boundedConstructible_fourierTransform_obj_of_boundedConstructible Λ π π' a Ψ b r
        K.obj K.property

end BoundedConstructible

end AlgebraicGeometry.Etale
