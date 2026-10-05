/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.EtaleCohomology.PoincareDuality.Classes
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect

/-!
# Finiteness: the global sections are perfect at the point

The duality statements pair the cohomology of `X` against itself, so they need that it is
*perfect at the point*: for `K ∈ D^b_{ctf}(X, Λ)`, both `RΓ_c(X, K)` and `RΓ(X, K)` are
bounded with finite cohomology of finite Tor amplitude. This file states that, for the
geometric fibre `X` of a `PoincareDualitySetting` and finite coefficients `Λ` whose exponent is
invertible on `s = Spec k` (the rendering of `ℓ ≠ p`).

As in `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`, `RΓ_c(X, K)` and `RΓ(X, K)`
are read one step earlier, as `Ra_! K` and `Ra_* K` in `D(s_ét, Λ)`. "Perfect point complex"
is rendered as dualizability (`CategoryTheory.IsDualizable`) in `D(s_ét, Λ)`, as everywhere in
the project (see `WeilConjectures.SixFunctors.Etale.Derived.Perfect`); the duals are then
dualizable by `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`.

## Main statements

At finite coefficients:
- `AlgebraicGeometry.Etale.exists_isZero_cohomologyClasses_rightDerivedLowerStar_of_lt`:
  `H^q(X, K)` vanishes outside a bounded range of degrees.
- `AlgebraicGeometry.Etale.module_finite_cohomologyClasses_rightDerivedLowerStar`:
  `H^q(X, K)` is a finite `Λ`-module.
- `AlgebraicGeometry.Etale.isDualizable_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.isDualizable_rightDerivedLowerStar`: `RΓ_c(X, K)` and `RΓ(X, K)`
  are perfect point complexes.

The compactly supported counterparts of the first two are
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt` and
`AlgebraicGeometry.Etale.finite_compactlySupportedCohomology`
(`sk-prop-sf-trace-perfectness`).

At the integral stage `𝒪_E`:
- `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar`: `Ra_!` and `Ra_*`
  preserve derived completeness.

## Implementation notes

The coefficient stages of the blueprint are `A_{E,n}`, `𝒪_E`, `E` and `ℚ̄_ℓ`. The finite
stage is `ModuleCat Λ` with `[Finite Λ]`. For `𝒪_E` only what the API expresses is stated, as
in `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`: that `Ra_!` and `Ra_*` restrict
to the derived-complete categories. *Not stated*: the common Tor amplitude of the reductions
over `𝒪_E` (the reductions `𝒪_E → A_{E,n}` are not functors between these categories here),
the finite-dimensionality over `E` (the `E` stage
`AlgebraicGeometry.DerivedCategoryDerivedCompleteRational` carries no `Rf_!`), and the
`ℚ̄_ℓ` stage, which does not exist in the repository.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section FiniteStage

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ} (S : PoincareDualitySetting k₀ d)
  (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]
  [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**Boundedness of ordinary cohomology.** For `K ∈ D^b_{ctf}(X, Λ)` on the geometric fibre `X`
of the setting, the cohomology `H^q(X, K)` — the degree `q` classes of `Ra_* K` in
`D(s_ét, Λ)` — vanishes for `q` outside a bounded range `[a, b]`. -/
theorem exists_isZero_cohomologyClasses_rightDerivedLowerStar_of_lt
    [HasCompactification (S.structureMorphism k)]
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K) :
    ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      Subsingleton (DerivedCategory.cohomologyClasses
        ((R((S.structureMorphism k)_*[ModuleCat.{u + 1} Λ])).obj K) q) :=
  sorry

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**Finiteness of ordinary cohomology.** For `K ∈ D^b_{ctf}(X, Λ)` every cohomology module
`H^q(X, K)` — the degree `q` classes of `Ra_* K` in `D(s_ét, Λ)` — is a finite `Λ`-module. -/
theorem module_finite_cohomologyClasses_rightDerivedLowerStar
    [HasCompactification (S.structureMorphism k)]
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K) (q : ℤ) :
    Module.Finite Λ (DerivedCategory.cohomologyClasses
      ((R((S.structureMorphism k)_*[ModuleCat.{u + 1} Λ])).obj K) q) :=
  sorry

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ_c(X, K)` is a perfect point complex.** For `K ∈ D^b_{ctf}(X, Λ)` the compactly supported
direct image `Ra_! K` is dualizable in `D(s_ét, Λ)`. Its dual is then dualizable too, by
`AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`. -/
theorem isDualizable_rightDerivedLowerShriek
    [HasCompactification (S.structureMorphism k)]
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K) :
    IsDualizable ((R(S.structureMorphism k)_![ModuleCat.{u + 1} Λ]).obj K) :=
  sorry

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ(X, K)` is a perfect point complex.** For `K ∈ D^b_{ctf}(X, Λ)` the direct image
`Ra_* K` is dualizable in `D(s_ét, Λ)`. Its dual is then dualizable too, by
`AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`. -/
theorem isDualizable_rightDerivedLowerStar
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K) :
    IsDualizable ((R((S.structureMorphism k)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

end FiniteStage

section IntegralStage

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ}
  (S : PoincareDualitySetting k₀ d) (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]

set_option quotPrecheck false in
set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. -/
local notation "𝒪Mod" => ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ_c` at the integral stage.** At `Λ = 𝒪_E`, the compactly supported direct image `Ra_!`
carries derived-complete objects of `D(X_ét, 𝒪_E)` to derived-complete objects of
`D(s_ét, 𝒪_E)`, so that `RΓ_c(X, K)` is an object of the adic category `D_comp(s, 𝒪_E)`. -/
theorem derivedCompleteIntegral_rightDerivedLowerShriek
    [HasCompactification (S.structureMorphism k)]
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology 𝒪Mod))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral
      (S.geometricFiber k).smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral (Spec (CommRingCat.of k)).smallEtaleTopology
      l E ((R(S.structureMorphism k)_![𝒪Mod]).obj K) :=
  sorry

/-- Blueprint `sk-lem-finite`: Finiteness: the global sections are perfect at the point.

**`RΓ` at the integral stage.** At `Λ = 𝒪_E`, the direct image `Ra_*` carries derived-complete
objects of `D(X_ét, 𝒪_E)` to derived-complete objects of `D(s_ét, 𝒪_E)`. -/
theorem derivedCompleteIntegral_rightDerivedLowerStar
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology 𝒪Mod))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral
      (S.geometricFiber k).smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral (Spec (CommRingCat.of k)).smallEtaleTopology
      l E ((R((S.structureMorphism k)_*[𝒪Mod])).obj K) :=
  sorry

end IntegralStage

end Etale

end AlgebraicGeometry
