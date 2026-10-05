/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

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
  `a : X ⟶ Spec k` separated of finite type over a field.
- `AlgebraicGeometry.Etale.derivedCompleteIntegral_coefficientDual`: so does the coefficient
  dual `K ↦ K^∨`.

## Implementation notes

The blueprint states `sk-thm-transport` at the three stages `𝒪_E`, `E` and `ℚ̄_ℓ`. Only the
integral stage `𝒪_E` is stated here, and only its non-formal part: that the operations preserve
derived completeness. The `E` stage would be the image of these statements under the
rationalization `AlgebraicGeometry.DerivedCategoryDerivedCompleteRational.fromIntegral`, and the
`ℚ̄_ℓ` stage their colimit over finite extensions `E/ℚ_ℓ`, a colimit category the repository
does not have; neither is stated. Which coefficient category carries the `E` and `ℚ̄_ℓ` stages
is not decided here.
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

/-- The derived category `D(X_ét, 𝒪_E)` of étale sheaves of `𝒪_E`-modules on `X`. -/
local notation "𝐃(" X ", " "𝒪_E" ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (PadicAlgCl.integersModuleCat l E))

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**`Rf_*` preserves derived completeness** (integral stage only). For every morphism
`f : X ⟶ Y`, the derived direct image `Rf_*` carries derived-complete objects of
`D(X_ét, 𝒪_E)` to derived-complete objects of `D(Y_ét, 𝒪_E)`. -/
theorem derivedCompleteIntegral_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : 𝐃(X, 𝒪_E))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R((f)_*[PadicAlgCl.integersModuleCat.{u} l E])).obj K) :=
  -- Proof sketch: derived completeness of `M` is the vanishing of `RHom(E', M)` for the
  -- constant complexes `E'` on `𝒪_E[1/ℓ]`-modules, and
  -- `RHom(E'_Y, Rf_* K) = Rf_* RHom(Lf^* E'_Y, K)` with `Lf^* E'_Y = E'_X`.
  sorry

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**`RΓ_c` preserves derived completeness** (integral stage only). For `a : X ⟶ Spec k`
separated of finite type over a field, `Ra_!` carries derived-complete objects of
`D(X_ét, 𝒪_E)` to derived-complete objects of `D(Spec k_ét, 𝒪_E)`, so that `RΓ_c(X, K)` is
an object of the adic category `D_comp(Spec k, 𝒪_E)`. -/
theorem derivedCompleteIntegral_rightDerivedLowerShriek {X : Scheme.{u}} {k : Type u} [Field k]
    (a : X ⟶ Spec (.of k)) [HasCompactification a] [QuasiCompact a] (K : 𝐃(X, 𝒪_E))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral (Spec (.of k)).smallEtaleTopology l E
      ((R(a)_![PadicAlgCl.integersModuleCat.{u} l E]).obj K) :=
  -- Proof sketch: `Ra_! = Rg_* j_!` for the chosen compactification, and `Ra_!` has finite
  -- cohomological dimension.
  sorry

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**The dual at the integral stage.** The coefficient dual `K^∨ = RHom(K, Λ_X)` of a
derived-complete object of `D(X_ét, 𝒪_E)` is derived complete. -/
theorem derivedCompleteIntegral_coefficientDual {X : Scheme.{u}} (K : 𝐃(X, 𝒪_E))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((DerivedCategory.coefficientDual (PadicAlgCl.integersModuleCat.{u} l E) X).obj (op K)) :=
  -- Proof sketch: `Λ_X = 𝒪_E` is derived complete and `RHom(K, -)` preserves derived-complete
  -- objects, being a right adjoint.
  sorry

end Etale

end AlgebraicGeometry
