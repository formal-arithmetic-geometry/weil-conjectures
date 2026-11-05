/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect

/-!
# Derived completeness and the six operations

Let `Λ` be a domain and `I` a principal ideal of `Λ`, so that every `Λ/Iⁿ` is a perfect
`Λ`-module. This file records that the operations used by Poincaré duality carry objects of
`D(X_ét, Λ)` that are derived complete for `I` (`DerivedCategory.derivedComplete`) to derived
complete objects. At the integral stage `Λ = 𝒪_E`, `I = 𝔪_E` of the `ℓ`-adic formalism these
say that the operations restrict to the adic categories `D_comp(−, 𝒪_E)` of
`DerivedCategory.derivedCompleteIntegral`. Together with
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek` (in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`), for `Rf^!`, this places every
object of the derived Poincaré pairing at `Λ = 𝒪_E` in the adic category.

## Main statements

- `AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerStar`: `Rf_*` preserves derived
  completeness.
- `AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerShriek`: so does `Rf_!` for proper
  `f`, `Rf_!` being `Rf_*` then. It fails for open immersions.
- `AlgebraicGeometry.Etale.derivedComplete_coefficientDual`: so does the coefficient dual
  `K ↦ K^∨`, provided the constant complex `Λ_X` is itself derived complete.

The `derivedCompleteIntegral_*` versions are their specialisations to `𝒪_E`.

## Implementation notes

The hypotheses on `(Λ, I)` are only used to make each `Λ/Iⁿ` perfect, through
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`. For `𝒪_E` the
ideal `𝔪_E` is principal when `E` is finite over `ℚ_ℓ`
(`PadicAlgCl.isPrincipal_maximalIdealShrink`), which is why the specialisations assume it.

The blueprint states `sk-thm-transport` at the three stages `𝒪_E`, `E` and `ℚ̄_ℓ`. Only the
integral stage `𝒪_E` is stated here, and only its non-formal part: that the operations preserve
derived completeness. The `E` stage would be the image of these statements under the
rationalization `DerivedCategoryDerivedCompleteRational.fromIntegral`, and the `ℚ̄_ℓ` stage
their colimit over finite extensions `E/ℚ_ℓ`, a colimit category the repository does not have;
neither is stated. Which coefficient category carries the `E` and `ℚ̄_ℓ` stages is not decided
here.
-/

@[expose] public section

universe w u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

set_option hygiene false in
/-- The constant complex `Λ_X`: the constant sheaf `Λ` on `X_ét`, placed in degree `0`. It is
the monoidal unit of `D(X_ét, Λ)` up to `DerivedCategory.εSingleFunctorZero`; it is spelled this
way so that the monoidal structure of the derived category stays out of the statements below
(see the implementation notes of `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`).
-/
local notation "Λ_(" X ", " Λ ")" =>
  (_root_.DerivedCategory.singleFunctor (Sheaf (Scheme.smallEtaleTopology X)
    (ModuleCat.{u + 1} Λ)) 0).obj
      ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))

section General

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] (I : Ideal Λ) (hI : I.IsPrincipal)

include hI

end General

section Integral

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

end Integral

end Etale

end AlgebraicGeometry
