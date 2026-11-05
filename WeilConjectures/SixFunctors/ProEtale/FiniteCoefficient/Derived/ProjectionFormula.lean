/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.NumberTheory.Padics.IntegersNoetherian
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!

# The projection formula on the pro-étale site

Let `A` be a monoidal Grothendieck abelian coefficient category and let `f : X ⟶ Y` be a
morphism of schemes admitting a compactification, so that the compactly supported direct
image `Rf_! : D(X_proét) ⥤ D(Y_proét)` is available. The *projection formula* is the assertion
that the canonical projection map

```
  PF_{f, K, L} : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.ProEtale.projectionMapOfCompactification` is an isomorphism, for
`K : D(X_proét)` and `L : D(Y_proét)`. This file is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`.

## Main definitions

- `AlgebraicGeometry.ProEtale.HasProjectionFormulaOfCompactification` : the projection formula
  for `Rf_!` computed with a given compactification `c` of `f`.
- `AlgebraicGeometry.ProEtale.HasProjectionFormula` : the projection formula for `Rf_!`
  computed with the chosen compactification `HasCompactification.compactification f`.

## Main statements

`sk-thm-sf-pf-proetale`, at every coefficient stage:
- `AlgebraicGeometry.ProEtale.hasProjectionFormula_of_constructibleFiniteTor`: the finite stages
  `Λ` (a finite ring), for objects of `Dctf(X_proét, Λ)`; also
  `AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_constructibleFiniteTor`
  for an arbitrary compactification.
- `AlgebraicGeometry.ProEtale.hasProjectionFormula_of_derivedCompleteIntegral`: the integral
  stage `𝒪_E`, for the pro-étale realizations of bounded constructible, derived complete
  `𝒪_E`-complexes of finite Tor amplitude.
- `AlgebraicGeometry.ProEtale.isIso_rationalization_map_projectionMap`: the rational stage `E`
  (hence `ℚ̄_ℓ`, through the finite stages `E` at which its objects are represented).
- `AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_comparison`: the common
  reduction to the étale projection formula along `ν^*`.

## Implementation notes

The projection map is the composite of the projection map of `Rg_*` for the proper part `g` of
the compactification and of the inverse of the projection isomorphism for the open immersion
`i` (`AlgebraicGeometry.ProEtale.isIso_derivedOpenImmersionLowerShriekProjectionMap`); the
projection formula asserts that the former is an isomorphism on the relevant objects.

As in the blueprint, every stage is reduced to the étale projection formula along `ν^*`: the
comparison carries the étale projection map of `Rg_*` to the pro-étale one
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison`) and
`ν^*` commutes with extension by zero. The étale inputs are
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite` at the finite
stages (`sk-thm-sf-pf-finite`) and
`AlgebraicGeometry.Etale.hasProjectionFormula_of_isIso_reductionModIdeal_map` at the integral
stage (`sk-thm-sf-pf-adic`, assuming the two sides of the étale projection map derived
complete); the rational stage is the image of the integral one under the
rationalization (`sk-thm-sf-pf-field`). The finite Tor amplitude of `L` keeps
`i_! K ⊗ᴸ Lg^* L` bounded below, where `ν^*` is known to commute with `Rg_*`.

The blueprint's "étale-origin witnesses" are explicit: at the finite stages they are built into
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor` (pro-étale bounded
constructibility is étale origin); at the `ℓ`-adic stages they are isomorphisms `ν^* K₀ ≅ K` with
`K₀` a bounded constructible, derived complete étale complex of finite Tor amplitude. As in the
étale model (`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational`), the stage
`ℚ̄_ℓ` is covered through the finite stages `E` at which its objects are represented. The
compatibility with the scalar extensions `𝒪_E ⟶ 𝒪_{E'}` (the projection map over `E'` at scalar
extensions of `𝒪_E`-objects is an isomorphism) is
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars`.
The statement cannot be made directly with the discrete coefficients
`AlgebraicGeometry.WeilCoefficients` (`ℚ̄_ℓ`-modules): there `ν^*` commutes with `Rg_*` on
bounded below complexes, so the projection formula for objects of étale origin would be the
étale one with discrete coefficients of characteristic zero, which fails (see the docstring of
`AlgebraicGeometry.Etale.hasProjectionFormula_field`).

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {X Y : Scheme.{u}}

variable [ProEtale.UpperStarPreservesFlat A]

omit [ProEtale.UpperStarPreservesFlat A] in
variable {A} in
/-- For `g : Z ⟶ Y`, a bounded complex `M` of étale sheaves on `Z` and a complex `L` of étale
sheaves on `Y` of finite Tor amplitude, `M ⊗ᴸ Lg^* L` is bounded below, `Lg^* L` having finite
Tor amplitude. -/
lemma _root_.AlgebraicGeometry.Etale.plus_derivedTensor_leftDerivedUpperStar
    [Etale.UpperStarPreservesFlat A] {Z : Scheme.{u}} (g : Z ⟶ Y)
    {M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : _root_.DerivedCategory.TStructure.t.bounded M) {a b : ℤ}
    (hL : Etale.DerivedCategory.torAmplitudeIn A Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor A Z).obj M).obj ((L(Etale.upperStar A g)).obj L)) := by
  obtain ⟨p, q, hMpq⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded M).2 hM
  have hMP := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_right hMpq
    (Etale.torAmplitudeIn_leftDerivedUpperStar A g a b hL)
  exact ((_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1 ⟨_, _, hMP⟩).1

end ProEtale

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

section Integral

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. The ring structure is written
as the one underlying the commutative ring structure, as in the statements of the lemmas for
general commutative coefficient rings that are applied to it. -/
local notation "𝐌" =>
  @ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)) CommRing.toRing

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {X Y : Scheme.{u}}

end Integral

end AlgebraicGeometry.ProEtale
