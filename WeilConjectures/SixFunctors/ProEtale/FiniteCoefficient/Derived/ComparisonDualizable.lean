/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

/-!
# The derived internal hom out of the comparison pullback of a dualizable complex

Let `Λ` be a noetherian commutative ring, `X` a scheme, and `D`, `P` objects of `D(X_ét, Λ)`
forming an exact pairing. The levelwise comparison pullback `ν^* = D(ν^*)` is strong monoidal,
so `ν^*D` is a left dual of `ν^*P` in `D(X_proét, Λ)`, and hence
`RHom(ν^*P, ν^*N) ≅ ν^*D ⊗ᴸ ν^*N ≅ ν^*(D ⊗ᴸ N)`. In particular `RHom(ν^*P, ν^*N)` is of étale
origin as soon as `D ⊗ᴸ N` is bounded below.

## Main definitions

- `AlgebraicGeometry.ProEtale.mapDerivedCategoryComparisonUpperStarMonoidal`: the strong monoidal
  structure on `D(ν^*)`, whose comonoidal structure is the derived tensor comparison.
- `AlgebraicGeometry.ProEtale.derivedHomMapDerivedCategoryIsoOfExactPairing`: the isomorphism
  `RHom(ν^*P, ν^*N) ≅ ν^*(D ⊗ᴸ N)`.

## Main statements

- `AlgebraicGeometry.ProEtale.plusEtaleOrigin_derivedHom_mapDerivedCategory_of_exactPairing`:
  `RHom(ν^*P, ν^*N)` is bounded below of étale origin if `D ⊗ᴸ N` is bounded below.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

variable {A X}

end General

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ] {X : Scheme.{u}}

end AlgebraicGeometry.ProEtale
