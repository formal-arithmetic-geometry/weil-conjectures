/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Group.AddChar
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!

# The Artin–Schreier sheaf

Let `X` be a scheme of characteristic `p`, let `Ψ` be an additive character of `ℤ/p` with
values in a coefficient ring `Λ` in which `p` is invertible and let `f ∈ Γ(X, 𝒪_X)`. The
*Artin–Schreier covering* attached to `f` is the finite étale `ℤ/p`-torsor
`π : Y = Spec_X 𝒪_X[T]/(Tᵖ - T - f) ⟶ X`, and the *Artin–Schreier sheaf*
`ℒ_{Ψ, f} := e_Ψ π_* Λ` is the `Ψ`-isotypic component of its pushforward, cut out by the
idempotent `e_Ψ = p⁻¹ ∑_{a ∈ ℤ/p} Ψ(-a) σ_a`. It is a lisse sheaf of rank one, that is, an
invertible object of the category of étale sheaves; it turns addition of functions into
tensor product of sheaves, and multiplication of characters likewise.

This file states those facts; the constructions themselves are `sorry`.

## Main definitions

- `AlgebraicGeometry.Etale.artinSchreierSheaf`: the Artin–Schreier sheaf `ℒ_{Ψ, f}`.
- `AlgebraicGeometry.Etale.artinSchreierSheafAddIso`: `ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`.
- `AlgebraicGeometry.Etale.artinSchreierSheafZeroIso`: `ℒ_{Ψ, 0} ≅ Λ`.
- `AlgebraicGeometry.Etale.artinSchreierSheafMulIso`: `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`.
- `AlgebraicGeometry.Etale.artinSchreierSheafOneIso`: `ℒ_{1, f} ≅ Λ`.
- `AlgebraicGeometry.Etale.artinSchreierSheafNegIso` and
  `AlgebraicGeometry.Etale.artinSchreierSheafInvIso`: the two inversion formulas
  `ℒ_{Ψ, f} ⊗ ℒ_{Ψ, -f} ≅ Λ` and `ℒ_{Ψ, f} ⊗ ℒ_{Ψ⁻¹, f} ≅ Λ`, corollaries of the four
  isomorphisms above.

## Main statements

- `AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf`: `ℒ_{Ψ, f}` is lisse.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

The subsection `sk-lem-as-properties` also contains the construction of the Artin–Schreier
covering itself, the decomposition `π_* Λ ≅ ⨁_χ ℒ_χ` of its pushforward, the trace function
of `ℒ_{Ψ, a f}` and the cohomology of the affine line with coefficients in `ℒ_{Ψ, a x}`.
Those are deferred: they are the inputs to the *proofs* of the statements of this block, and
the first two of them need the finite étale relative spectrum, which is not yet available.

## Implementation notes

`p` is required to be invertible in `Λ` throughout: the idempotent `e_Ψ` that defines
`ℒ_{Ψ, f}` is `p⁻¹ ∑_a Ψ(-a) σ_a`, and without it the pushforward `π_* Λ` has no isotypic
decomposition — for `Λ = ℤ/p` every statement below is false.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {p : ℕ} [Fact p.Prime] {Λ : Type (u + 1)} [CommRing Λ] [Invertible (p : Λ)]
variable (X : Scheme.{u}) [CharP Γ(X, ⊤) p]

/-- For a scheme `X` of characteristic `p` and a global function `f ∈ Γ(X, 𝒪_X)`, the
Artin–Schreier covering `π : Y = Spec_X 𝒪_X[T]/(Tᵖ - T - f) ⟶ X` is finite étale of degree
`p` with automorphism group `ℤ/p` acting by `σ_a : T ↦ T + a`. The *Artin–Schreier sheaf*
`ℒ_{Ψ, f}` is the `Ψ`-isotypic component `e_Ψ π_* Λ` of the pushforward of the constant
sheaf, where `e_Ψ = p⁻¹ ∑_{a ∈ ℤ/p} Ψ(-a) σ_a`; equivalently, the subsheaf on which each
`σ_a` acts by `Ψ(a)`. The idempotent uses the character `Ψ` of `ℤ/p` itself, not the
restriction to `ℤ/p` of an additive character of the base field.
(sketch blueprint: `sk-def-as`) -/
noncomputable def artinSchreierSheaf (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  sorry

/-- The Artin–Schreier sheaf of the zero function is the constant sheaf `Λ`. Together with
`AlgebraicGeometry.Etale.artinSchreierSheafAddIso` this says that `ℒ_{Ψ, f}` is an
invertible object of the category of étale sheaves — a lisse sheaf of rank one — with
inverse `ℒ_{Ψ, -f}`.
(sketch blueprint: `sk-lem-as-properties`) -/
noncomputable def artinSchreierSheafZeroIso (Ψ : AddChar (ZMod p) Λ) :
    artinSchreierSheaf X Ψ 0 ≅ 𝟙_ _ :=
  sorry

/-- The Artin–Schreier sheaf of the trivial character is the constant sheaf `Λ`: the
`1`-isotypic component of `π_* Λ` is the sheaf of `ℤ/p`-invariants, which is `Λ` because `π`
is a `ℤ/p`-torsor.
(sketch blueprint: `sk-lem-as-properties`) -/
noncomputable def artinSchreierSheafOneIso (f : Γ(X, ⊤)) :
    artinSchreierSheaf X (1 : AddChar (ZMod p) Λ) f ≅ 𝟙_ _ :=
  sorry

variable {X}

/-- The Artin–Schreier sheaf is lisse: the covering is finite étale of degree `p`, so its
pushforward decomposes as `π_* Λ ≅ ⨁_{χ} ℒ_χ` over the characters of `ℤ/p`, each summand
being locally constant of rank one.
(sketch blueprint: `sk-lem-as-properties`) -/
instance isLocallyConstantSheaf_artinSchreierSheaf (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheaf X Ψ f) :=
  sorry

/-- The Artin–Schreier sheaf turns addition of functions into tensor product of sheaves,
`ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`.
(sketch blueprint: `sk-lem-as-properties`) -/
noncomputable def artinSchreierSheafAddIso (Ψ : AddChar (ZMod p) Λ) (f g : Γ(X, ⊤)) :
    artinSchreierSheaf X Ψ f ⊗ artinSchreierSheaf X Ψ g ≅ artinSchreierSheaf X Ψ (f + g) :=
  sorry

/-- The Artin–Schreier sheaf turns multiplication of characters into tensor product of
sheaves, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`: both sides are isotypic components of the
pushforward along the same covering.
(sketch blueprint: `sk-lem-as-properties`) -/
noncomputable def artinSchreierSheafMulIso (Ψ Ψ' : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    artinSchreierSheaf X Ψ f ⊗ artinSchreierSheaf X Ψ' f ≅ artinSchreierSheaf X (Ψ * Ψ') f :=
  sorry

/-- The inverse of `ℒ_{Ψ, f}` is `ℒ_{Ψ, -f}`. -/
noncomputable def artinSchreierSheafNegIso (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    artinSchreierSheaf X Ψ f ⊗ artinSchreierSheaf X Ψ (-f) ≅ 𝟙_ _ :=
  artinSchreierSheafAddIso Ψ f (-f) ≪≫
    eqToIso (congrArg (artinSchreierSheaf X Ψ) (add_neg_cancel f)) ≪≫
      artinSchreierSheafZeroIso X Ψ

/-- The inverse of `ℒ_{Ψ, f}` is also `ℒ_{Ψ⁻¹, f}`; combined with
`AlgebraicGeometry.Etale.artinSchreierSheafNegIso` this is the identification
`ℒ_{Ψ, -f} ≅ ℒ_{Ψ⁻¹, f}` used for the kernel of the Fourier transform attached to the
inverse character. -/
noncomputable def artinSchreierSheafInvIso (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    artinSchreierSheaf X Ψ f ⊗ artinSchreierSheaf X Ψ⁻¹ f ≅ 𝟙_ _ :=
  artinSchreierSheafMulIso Ψ Ψ⁻¹ f ≪≫
    eqToIso (congrArg (artinSchreierSheaf X · f) (mul_inv_cancel Ψ)) ≪≫
      artinSchreierSheafOneIso X f

end AlgebraicGeometry.Etale
