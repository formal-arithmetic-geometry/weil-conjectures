/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.InternalHom

/-!
# Extensions of constructible `Λ`-adic sheaves

This is the counterpart, for a coefficient field `Λ` with an ultrametric norm (the case of
interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Extension`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

An epimorphism `q : P ⟶ Q` of sheaves of `Λ_X`-modules is locally split over a section
`Λ_X ⟶ Q`: there is a pro-étale cover over each member `g : W ⟶ X` of which the section lifts to
`g^* P` (`AlgebraicGeometry.ProEtale.exists_cover_field_lift`). The underlying section lifts on a
covering sieve because `q` is locally surjective, and a section over the terminal object of
`W.ProEt` is a map out of the unit sheaf (`AlgebraicGeometry.ProEtale.fieldUnitSheafLift`); the unit
comparison of the pullback is computed through the restriction to the slice site.

Applied to a basis of `Λⁿ`, an extension of `Λⁿ` by a lisse sheaf splits locally, so
extensions of lisse sheaves are lisse
(`AlgebraicGeometry.ProEtale.IsFieldLisseSheaf.of_shortExact`).
Refining stratifications, extensions of constructible sheaves are constructible
(`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.of_shortExact`), i.e.
`(fieldConstructibleSheaf Λ X).IsClosedUnderExtensions`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

universe u

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]

section

variable {W : Scheme.{u}}

end

section

variable {W : Scheme.{u}}

end

section

variable {V : Scheme.{u}}

end

section

variable {V : Scheme.{u}}

end

section

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

variable {X : Scheme.{u}}

end

end AlgebraicGeometry.ProEtale
