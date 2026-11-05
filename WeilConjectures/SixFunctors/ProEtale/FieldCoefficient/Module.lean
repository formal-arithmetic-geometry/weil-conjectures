/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Ring

/-!
# Sheaves of modules over the constant sheaf

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Module`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

Let `X` be a scheme and `Λ_X = AlgebraicGeometry.ProEtale.fieldConstantSheaf Λ X` the sheaf of
rings of continuous `Λ`-valued functions on the pro-étale site of `X`. Following
Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8), the `Λ`-adic sheaves on `X` are the
sheaves of `Λ_X`-modules: the module objects over the monoid `Λ_X` of the monoidal category
of sheaves of `Λ`-modules (`AlgebraicGeometry.ProEtale.FieldSheaf`). This is a Grothendieck
abelian category, in which kernels, cokernels and extensions are computed on the underlying
sheaves of `Λ`-modules; but its extensions are those of `Λ_X`-modules, not of sheaves of
modules over the discrete field `Λ`.

For a morphism `g : Z ⟶ Y` the pushforward `g_*` and the pullback `g^*` of sheaves of
`Λ`-modules lift to sheaves of modules over the constant sheaves `Λ_X`: `g_*` is lax
monoidal, so `g_* M` is a `g_* Λ_Z`-module, hence a `Λ_Y`-module along the ring morphism
`Λ_Y ⟶ g_* Λ_Z` (`AlgebraicGeometry.ProEtale.isMonHom_fieldConstantSheafToLowerStar`); and
`g^*` is monoidal, so `g^* M` is a `g^* Λ_Y`-module, hence a `Λ_Z`-module along the ring
isomorphism `g^* Λ_Y ≅ Λ_Z`. The underlying sheaves are those of the pushforward and the
pullback of sheaves of `Λ`-modules, so both functors are exact, and they are adjoint
(`AlgebraicGeometry.ProEtale.fieldUpperStarLowerStarAdjunction`).

## Main definitions

- `AlgebraicGeometry.ProEtale.FieldSheaf`: sheaves of `Λ_X`-modules on `X_proét`.
- `AlgebraicGeometry.ProEtale.FieldSheaf.unit`: the constant sheaf as a module over
  itself.
- `AlgebraicGeometry.ProEtale.fieldLowerStar`, `AlgebraicGeometry.ProEtale.fieldUpperStar`: `g_*`
  and `g^*`, with notations `(g)_*ᶠ[Λ]` and `(g)^*ᶠ[Λ]`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

variable {Λ}

namespace FieldSheaf

end FieldSheaf

section Functors

open scoped Obj

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

@[inherit_doc fieldLowerStar]
scoped notation "(" g ")_*ᶠ[" Λ "]" => fieldLowerStar Λ g

@[inherit_doc fieldUpperStar]
scoped notation "(" g ")^*ᶠ[" Λ "]" => fieldUpperStar Λ g

end Functors

section Compat

variable (Λ)

end Compat

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open scoped Obj

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

section Isos

end Isos

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.FieldSheaf

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ] {X : Scheme.{u}}

end AlgebraicGeometry.ProEtale.FieldSheaf
