/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect

/-!
# Derived completeness and the six operations at the integral stage

At the integral stage `𝒪_E` of the `ℓ`-adic formalism the coefficients are the derived-complete
objects `DerivedCategory.derivedCompleteIntegral` of `D(X_ét, 𝒪_E)`. This file records that the
operations used by Poincaré duality preserve them, so that they restrict to the adic categories
`D_comp(−, 𝒪_E)`. Together with
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek` this places every
object of the derived Poincaré pairing at `Λ = 𝒪_E` in the adic category.

## Main statements

- `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar`: `Rf_*` preserves
  derived completeness.
- `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerShriek`: so does `Ra_!` for
  `a : X ⟶ Spec k` separated of finite type.
- `AlgebraicGeometry.Etale.derivedCompleteIntegral_coefficientDual`: so does the coefficient
  dual `K ↦ K^∨`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E]

/-- **`Rf_*` preserves derived completeness.** For every morphism `f : X ⟶ Y`, the derived
direct image `Rf_*` carries derived-complete objects of `D(X_ét, 𝒪_E)` to derived-complete
objects of `D(Y_ét, 𝒪_E)`. Derived completeness of `M` is the vanishing of
`RHom(E', M)` for the constant complexes `E'` on `𝒪_E[1/ℓ]`-modules, and
`RHom(E'_Y, Rf_* K) = Rf_* RHom(Lf^* E'_Y, K)` with `Lf^* E'_Y = E'_X`. -/
theorem derivedCompleteIntegral_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (PadicAlgCl.IntegralCoefficients.{_, u} l E)))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R((f)_*[PadicAlgCl.IntegralCoefficients.{_, u} l E])).obj K) :=
  sorry

/-- **`RΓ_c` preserves derived completeness.** For `a : X ⟶ Spec k` separated of finite type
over a separably closed field, `Ra_!` carries derived-complete objects of `D(X_ét, 𝒪_E)` to
derived-complete objects of `D(Spec k_ét, 𝒪_E)`, so that `RΓ_c(X, K)` is an object of the
adic category `D_comp(Spec k, 𝒪_E)`. `Ra_! = Rg_* j_!` for the chosen compactification, and
`Ra_!` has finite cohomological dimension. -/
theorem derivedCompleteIntegral_rightDerivedLowerShriek {X : Scheme.{u}} {k : Type u} [Field k]
    [IsSepClosed k] (a : X ⟶ Spec (.of k)) [HasCompactification a] [QuasiCompact a]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (PadicAlgCl.IntegralCoefficients.{_, u} l E)))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral (Spec (.of k)).smallEtaleTopology l E
      ((R(a)_![PadicAlgCl.IntegralCoefficients.{_, u} l E]).obj K) :=
  sorry

/-- **The dual at the integral stage.** The coefficient dual `K^∨ = RHom(K, Λ_X)` of a
derived-complete object of `D(X_ét, 𝒪_E)` is derived complete: `Λ_X = 𝒪_E` is derived
complete and `RHom(K, -)` preserves derived-complete objects, being a right adjoint. -/
theorem derivedCompleteIntegral_coefficientDual {X : Scheme.{u}}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (PadicAlgCl.IntegralCoefficients.{_, u} l E)))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((DerivedCategory.coefficientDual (PadicAlgCl.IntegralCoefficients.{_, u} l E) X).obj
        (op K)) :=
  sorry

end Etale

end AlgebraicGeometry
