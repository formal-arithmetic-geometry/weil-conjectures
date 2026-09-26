/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!

# The Artin–Schreier sheaf

Let `X` be a scheme of characteristic `p`, let `Ψ` be an additive character of `ℤ/p` with
values in a coefficient ring `Λ` and let `f ∈ Γ(X, 𝒪_X)`. The *Artin–Schreier covering*
attached to `f` is the finite étale `ℤ/p`-torsor
`π : Y = Spec_X 𝒪_X[T]/(Tᵖ - T - f) ⟶ X`, and the *Artin–Schreier sheaf*
`ℒ_{Ψ, f} := e_Ψ π_* Λ` is the `Ψ`-isotypic component of its pushforward, cut out by the
idempotent `e_Ψ = p⁻¹ ∑_{a ∈ ℤ/p} Ψ(-a) σ_a`. It is a lisse sheaf of rank one, that is, an
invertible object of the category of étale sheaves, and it turns addition of functions into
tensor product of sheaves.

This file states those facts; the constructions themselves are `sorry`.

## Main definitions

- `AlgebraicGeometry.Etale.artinSchreierSheaf`: the Artin–Schreier sheaf `ℒ_{Ψ, f}`.

## Main statements

- `AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf`: `ℒ_{Ψ, f}` is lisse.
- `AlgebraicGeometry.Etale.artinSchreierSheafAdd`: `ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`.
- `AlgebraicGeometry.Etale.artinSchreierSheafZero`: `ℒ_{Ψ, 0}` is the unit sheaf, so that
  `ℒ_{Ψ, f}` is invertible with inverse `ℒ_{Ψ, -f}`.

Multiplicativity in the character, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`, is stated for the
Fourier kernel in `WeilConjectures.FourierTransform.Defs`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {p : ℕ} [Fact p.Prime] {Λ : Type (u + 1)} [CommRing Λ]
variable {X : Scheme.{u}} [CharP Γ(X, ⊤) p]

/-- Blueprint `sk-def-as`: The Artin–Schreier sheaf.

For a scheme `X` of characteristic `p` and a global function `f ∈ Γ(X, 𝒪_X)`, the
Artin–Schreier covering `π : Y = Spec_X 𝒪_X[T]/(Tᵖ - T - f) ⟶ X` is finite étale of degree
`p` with automorphism group `ℤ/p` acting by `σ_a : T ↦ T + a`. The Artin–Schreier sheaf
`ℒ_{Ψ, f}` is the `Ψ`-isotypic component `e_Ψ π_* Λ` of the pushforward of the constant
sheaf, where `e_Ψ = p⁻¹ ∑_{a ∈ ℤ/p} Ψ(-a) σ_a`; equivalently, the subsheaf on which each
`σ_a` acts by `Ψ(a)`. The idempotent uses the character `Ψ` of `ℤ/p` itself, not the
restriction to `ℤ/p` of an additive character of the base field. -/
noncomputable def artinSchreierSheaf (X : Scheme.{u}) [CharP Γ(X, ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  sorry

/-- Blueprint `sk-lem-as-properties`: The Artin–Schreier sheaf is a lisse character sheaf.

The Artin–Schreier covering is finite étale of degree `p`, so its pushforward decomposes
as `π_* Λ ≅ ⨁_{χ} ℒ_χ` over the characters of `ℤ/p`, each summand being lisse of rank
one. In particular `ℒ_{Ψ, f}` is lisse. -/
theorem isLocallyConstantSheaf_artinSchreierSheaf (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheaf X Ψ f) :=
  sorry

/-- Blueprint `sk-lem-as-properties`: The Artin–Schreier sheaf is a lisse character sheaf.

The Artin–Schreier sheaf turns addition of functions into tensor product of sheaves,
`ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`. -/
noncomputable def artinSchreierSheafAdd (Ψ : AddChar (ZMod p) Λ) (f g : Γ(X, ⊤)) :
    artinSchreierSheaf X Ψ f ⊗ artinSchreierSheaf X Ψ g ≅ artinSchreierSheaf X Ψ (f + g) :=
  sorry

/-- Blueprint `sk-lem-as-properties`: The Artin–Schreier sheaf is a lisse character sheaf.

The Artin–Schreier sheaf of the zero function is the unit sheaf. Together with
`AlgebraicGeometry.Etale.artinSchreierSheafAdd` this says that `ℒ_{Ψ, f}` is an invertible
object of the category of étale sheaves — a lisse sheaf of rank one — with inverse
`ℒ_{Ψ, -f}`. -/
noncomputable def artinSchreierSheafZero (X : Scheme.{u}) [CharP Γ(X, ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) : artinSchreierSheaf X Ψ 0 ≅ 𝟙_ _ :=
  sorry

end AlgebraicGeometry.Etale
