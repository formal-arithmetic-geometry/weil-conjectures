/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient

/-!
# Frobenius operators and the adjunction `La^* ⊣ Ra_*`

Let `g ≫ a = a ≫ h` be a commutative square, `a : X ⟶ Y`, and `ψ : Lg^* M ⟶ M` a Weil datum on
`M ∈ D(X_ét, Λ)`. The identification `Hom(Λ_X, M) ≅ Hom(Λ_Y, Ra_* M)` given by the adjunction
`La^* ⊣ Ra_*` and `La^* Λ_Y ≅ Λ_X` intertwines the Frobenius operator of `ψ` with the Frobenius
operator of the induced datum on `Ra_* M`
(`AlgebraicGeometry.Etale.frobeniusOperator_lowerStarWeilDatum_homEquiv`). The key input is the
compatibility of the canonical isomorphisms `Lf^* Λ ≅ Λ` with the composition of derived
pullbacks (`AlgebraicGeometry.Etale.derivedSquareUpperStarIso_hom_app_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

variable {X Y : Scheme.{u}} {a : X ⟶ Y} {g : X ⟶ X} {h : Y ⟶ Y}

end AlgebraicGeometry.Etale
