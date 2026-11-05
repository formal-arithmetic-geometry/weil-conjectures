/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Proper base change modulo objects on which `ϖ` acts invertibly

Let `Λ` be a commutative ring and `ϖ ∈ Λ` a nonzerodivisor with `Λ ⧸ (ϖ)` finite (for instance
`Λ = 𝒪_E` and `ϖ` a uniformizer). Proper base change fails on `D(-_ét, Λ)`, but it holds up to
objects on which `ϖ` acts invertibly: for a cartesian square with `f` proper and `N` with
`Lg'^* N = 0`, the multiplication by `ϖ` on `Lg^* Rf_* N` is invertible
(`AlgebraicGeometry.Etale.isIso_smul_id_leftDerivedUpperStar_rightDerivedLowerStar`). The proof
passes to the finite ring `Λ ⧸ (ϖ)` through the derived coextension of scalars
`RHom_Λ(Λ ⧸ (ϖ), -)`, which commutes with `Rf_*` and detects the invertibility of `ϖ`.

Consequently the exchange map `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` of an extension by zero with a
proper direct image has cones on which `ϖ` acts invertibly
(`AlgebraicGeometry.Etale.isIso_smul_id_of_openImmersionLowerShriekLowerStarExchange`), so it
induces bijections on morphisms into objects killed by a power of `ϖ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section Coextension

variable {Λ : Type (u + 1)} [CommRing Λ]

variable {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
include hϖ

variable [Finite (Λ ⧸ Ideal.span {ϖ})]

end Coextension

section Cones

variable {Λ : Type (u + 1)} [CommRing Λ] (ϖ : Λ)

variable {ϖ}

end Cones

section Exchange

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  [Finite (Λ ⧸ Ideal.span {ϖ})]
include hϖ

end Exchange

section Composition

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  [Finite (Λ ⧸ Ideal.span {ϖ})] {J : Type*} [Category J] {S : Scheme.{u}}
  {P : J ⥤ 𝐃(S, Λ)}
  (hP : ∀ j, (_root_.DerivedCategory.smulInvertible S.smallEtaleTopology ϖ).rightOrthogonal
    (P.obj j))
include hϖ hP

end Composition

end Etale

end AlgebraicGeometry
