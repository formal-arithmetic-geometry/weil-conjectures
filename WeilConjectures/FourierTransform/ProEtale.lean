/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.AffineSpace
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Derived.KernelTransform

/-!

# The Fourier–Deligne transform on the pro-étale site

Let `π : V ⟶ S` and `π' : V' ⟶ S` be two `S`-schemes and `b ∈ Γ(V ×_S V', 𝒪)` a pairing. The
*pro-étale Fourier kernel* is `ν^* 𝒦_ψ`, the pullback along the comparison
`ν : (V ×_S V')_proét ⟶ (V ×_S V')_ét` of the étale Fourier kernel
`AlgebraicGeometry.Etale.fourierKernel`: the kernel has étale origin. The *pro-étale
Fourier–Deligne transform* of `K ∈ D(V_proét)` is the pro-étale kernel transform

`FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ ν^* 𝒦_ψ)[r]`.

Everything is over `ModuleCat Λ` for a commutative ring `Λ` in which `p` is invertible, as on
the étale side (`WeilConjectures.FourierTransform.Defs`).

## Main definitions

- `AlgebraicGeometry.ProEtale.fourierKernel`: the pro-étale Fourier kernel `ν^* 𝒦_ψ`.
- `AlgebraicGeometry.ProEtale.fourierTransform`: the pro-étale Fourier–Deligne transform.
- `AlgebraicGeometry.ProEtale.affineFourierTransform`: the transform of affine `n`-space with
  the standard pairing.
- `AlgebraicGeometry.ProEtale.fourierTransformBoundedConstructible`: the transform as a
  functor `Dᵇc_proét(V, Λ) ⥤ Dᵇc_proét(V', Λ)`.

## Main statements

- `AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_kernelTransform` and
  `AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_fourierTransform`: `D(ν^*)`
  intertwines the étale and pro-étale kernel transforms, hence the Fourier transforms.
- `AlgebraicGeometry.ProEtale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`:
  the pro-étale transform preserves bounded constructible complexes.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

## Coefficients

Coefficient classes (general / compactification-dependent / torsion) are those of
`WeilConjectures.FourierTransform.Defs`.

`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible` is the notion of étale
origin: `D(ν^*)` of a bounded constructible étale complex. It is the right notion only at
finite coefficient stages, so
`AlgebraicGeometry.ProEtale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`
and `AlgebraicGeometry.ProEtale.fourierTransformBoundedConstructible` are finite-stage
statements. The `ℓ`-adic transform is a separate construction.

## Implementation notes

The comparison theorems are stated with `Nonempty` and are not proved. Their missing inputs,
none of which is in the repository, are:

- `ν^*` commutes with the pullback `f^*`;
- `ν^*` is monoidal, so that `D(ν^*)` commutes with the derived tensor product;
- `ν^*` commutes with `Rf_! = Rg_* ∘ j_!`. On `D⁺` the direct image part is
  `AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar`;
  nothing covers `j_!`, nor the passage to unbounded complexes.

Given the comparison, preservation of bounded constructibility is a formal consequence of the
étale statement
`AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

/-- The comparison `D(ν^*)` intertwines the étale and pro-étale kernel transforms: for an étale
kernel `𝒦`,

`ν^* Φ_𝒦(K) ≅ Φ_{ν^* 𝒦}(ν^* K)`,

naturally in `K ∈ D(V_ét)`.

Class: general; decided by the compatibilities of `ν^*` with `f^*`, with the derived tensor
product (`ν^*` monoidal) and with `Rf_! = Rg_* ∘ j_!`, none of which is in the repository. On
`D⁺` the compatibility with `Rg_*` is
`AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar`;
nothing covers `j_!`.
(sketch blueprint: `sk-def-kernel`, pro-étale realisation) -/
theorem nonempty_iso_comparisonUpperStar_kernelTransform
    [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a : ℤ) :
    Nonempty (Etale.kernelTransform A π π' 𝒦 a ⋙ D(ν^*(V')[A]) ≅
      D(ν^*(V)[A]) ⋙ kernelTransform A π π' (D(ν^*(pullback π π')[A]).obj 𝒦) a) :=
  sorry

end General

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

/-- The *pro-étale Fourier kernel* `ν^* 𝒦_ψ` of a pairing `b ∈ Γ(V ×_S V', 𝒪)`: the pullback
along the comparison `ν` of the étale Fourier kernel `AlgebraicGeometry.Etale.fourierKernel`,
the Artin–Schreier sheaf `ℒ_{Ψ, b}` of the pairing. It is defined for every commutative ring
`Λ` in which `p` is invertible.
(sketch blueprint: `sk-def-kernel`, pro-étale realisation) -/
noncomputable def fourierKernel [CharP Γ(pullback π π', ⊤) p] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) :
    Sheaf (Scheme.ProEt.topology (pullback π π')) (ModuleCat.{u + 1} Λ) :=
  (ν^*(pullback π π')[ModuleCat.{u + 1} Λ]).obj (Etale.fourierKernel Λ π π' Ψ b)

/-- The *pro-étale Fourier–Deligne transform*

`FT_ψ(K) = Rp₂,!(p₁^* K ⊗ᴸ ν^* 𝒦_ψ)[r]`

of `K ∈ D(V_proét)`: the pro-étale kernel transform of the pro-étale Fourier kernel with
shift `r`, Laumon's normalization as on the étale side.
(sketch blueprint: `sk-def-ft`, pro-étale realisation) -/
noncomputable def fourierTransform [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology V') (ModuleCat.{u + 1} Λ)) :=
  kernelTransform (ModuleCat.{u + 1} Λ) π π'
    ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) r

/-- The comparison `D(ν^*)` intertwines the étale and pro-étale Fourier–Deligne transforms:

`ν^* FT_ψ(K) ≅ FT_ψ(ν^* K)`,

naturally in `K ∈ D(V_ét)`.

Class: general; decided by
`AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_kernelTransform`, whose inputs
(compatibility of `ν^*` with `f^*`, `⊗ᴸ` and `Rf_!`) are not in the repository, together with
the commutation of `D(ν^*)` with the inclusion of complexes concentrated in degree `0`, which
holds since `ν^*` is exact.
(sketch blueprint: `sk-def-ft`, pro-étale realisation) -/
theorem nonempty_iso_comparisonUpperStar_fourierTransform [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Nonempty (Etale.fourierTransform Λ π π' Ψ b r ⋙ D(ν^*(V')[ModuleCat.{u + 1} Λ]) ≅
      D(ν^*(V)[ModuleCat.{u + 1} Λ]) ⋙ fourierTransform Λ π π' Ψ b r) :=
  sorry

section BoundedConstructible

variable [Finite Λ] [HasInvertibleExponent Λ S]
  [CharP Γ(pullback π π', ⊤) p] [HasCompactification (pullback.snd π π')]
  [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]

/-- For `V'` locally of finite type over a field `k`, the pro-étale Fourier–Deligne transform
sends bounded constructible pro-étale complexes (those of étale origin) on `V` to bounded
constructible ones on `V'`. Since the bounded constructible pro-étale complexes are those of
étale origin, this is the finite-stage statement.

Class: torsion; decided by Deligne finiteness of `Rp₂,!` through
`AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`,
which needs `[Finite Λ] [HasInvertibleExponent Λ S]`, and by the comparison
`AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_fourierTransform`.
(sketch blueprint: `sk-prop-well-defined`, pro-étale realisation) -/
theorem boundedConstructible_fourierTransform_obj_of_boundedConstructible {k : Type u}
    [Field k] (aV' : V' ⟶ Spec (.of k)) [LocallyOfFiniteType aV'] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V'
      ((fourierTransform Λ π π' Ψ b r).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff _ _ K).1 hK
  obtain ⟨c⟩ := nonempty_iso_comparisonUpperStar_fourierTransform Λ π π' Ψ b r
  refine (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) V').prop_of_iso
    (c.app K' ≪≫ (fourierTransform Λ π π' Ψ b r).mapIso e) ?_
  exact DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
    (Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible Λ π π' aV' Ψ b r
      K' hK')

/-- For `V'` locally of finite type over a field, the pro-étale Fourier–Deligne transform as a
functor `Dᵇc_proét(V, Λ) ⥤ Dᵇc_proét(V', Λ)` on complexes of étale origin. This is the
finite-stage functor.

Class: torsion; decided by
`AlgebraicGeometry.ProEtale.boundedConstructible_fourierTransform_obj_of_boundedConstructible`,
which needs `[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-prop-well-defined`, pro-étale realisation) -/
noncomputable def fourierTransformBoundedConstructible
    (hV' : ∃ (k : Type u) (_ : Field k) (a : V' ⟶ Spec (.of k)), LocallyOfFiniteType a)
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Dᵇc_proét(V, ModuleCat.{u + 1} Λ) ⥤ Dᵇc_proét(V', ModuleCat.{u + 1} Λ) :=
  ObjectProperty.lift _
    (DerivedCategoryBoundedConstructible.ι (ModuleCat.{u + 1} Λ) V ⋙
      fourierTransform Λ π π' Ψ b r)
    fun K ↦ by
      obtain ⟨k, _, a, _⟩ := hV'
      exact boundedConstructible_fourierTransform_obj_of_boundedConstructible Λ π π' a Ψ b r
        K.obj K.property

end BoundedConstructible

section AffineSpace

open AffineSpace

variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The pro-étale Fourier–Deligne transform of affine `n`-space over `S`: the transform of
`AlgebraicGeometry.ProEtale.fourierTransform` for `𝔸(n; S)` paired with itself by the
standard pairing `⟨x, ξ⟩ = ∑ᵢ xᵢ ξᵢ` and shifted by the relative dimension `r = #n`.
(sketch blueprint: `sk-def-ft`, pro-étale realisation) -/
noncomputable def affineFourierTransform (Ψ : AddChar (ZMod p) Λ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (𝔸(n; S))) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology (𝔸(n; S))) (ModuleCat.{u + 1} Λ)) :=
  fourierTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S) (Fintype.card n)

end AffineSpace

end AlgebraicGeometry.ProEtale
