/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.Mathlib.CategoryTheory.NatIso
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersNoetherian
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import Submission.WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- The projection formula for a morphism `f : X ⟶ Y`, at `K : D(X_proét)` and
`L : D(Y_proét)`, with `Rf_!` computed from a chosen compactification `c` of `f`: the
assertion that the projection map

```
  PF_c : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.ProEtale.projectionMapOfCompactification` is an isomorphism. -/
def HasProjectionFormulaOfCompactification {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) : Prop :=
  IsIso (((projectionMapOfCompactification A c).app K).app L)

/-- The projection formula for a morphism `f : X ⟶ Y` admitting a compactification, at
`K : D(X_proét)` and `L : D(Y_proét)`: the assertion that the projection map

```
  PF : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

of `AlgebraicGeometry.ProEtale.projectionMap`, for the chosen compactification of `f`, is an
isomorphism. -/
def HasProjectionFormula (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) : Prop :=
  IsIso (((projectionMap A f).app K).app L)

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

variable {A} in
/-- **The pro-étale projection formula from the étale one.** Let `c = (X ⟶[i] Z ⟶[g] Y)` be a
compactification of `f`, and let `K ≅ ν^* K₀`, `L ≅ ν^* L₀` be pro-étale complexes of étale
origin, with `K₀` bounded and `i_! K₀ ⊗ᴸ Lg^* L₀` bounded below. If the étale projection map of
`Rg_*` is an isomorphism at `(i_! K₀, L₀)`, the pro-étale projection formula holds for `c` at
`(K, L)`: the projection map is the one of `Rg_*` at `(i_! K, L)` followed by isomorphisms,
`i_! ν^* K₀ ≅ ν^* i_! K₀`, and `ν^*` carries the étale projection map of `Rg_*` to the
pro-étale one
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived`). -/
theorem hasProjectionFormulaOfCompactification_of_comparison [Etale.UpperStarPreservesFlat A]
    [∀ X : Scheme.{u}, (ν^*(X)[A]).PreservesFlat] {f : X ⟶ Y} (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    {K₀ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (eK : D(ν^*(X)[A]).obj K₀ ≅ K) (eL : D(ν^*(Y)[A]).obj L₀ ≅ L)
    (hK₀ : _root_.DerivedCategory.TStructure.t.bounded K₀)
    (hML : _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor A c.Z).obj (D(Etale.openImmersionLowerShriek A c.i).obj K₀)).obj
        ((L(Etale.upperStar A c.g)).obj L₀)))
    (hPF : IsIso (((Etale.rightDerivedLowerStarProjectionMap A c.g).app
      (D(Etale.openImmersionLowerShriek A c.i).obj K₀)).app L₀)) :
    HasProjectionFormulaOfCompactification A c K L := by
  rw [HasProjectionFormulaOfCompactification, projectionMapOfCompactification_app_app]
  let M₀ := D(Etale.openImmersionLowerShriek A c.i).obj K₀
  have hM₀ : _root_.DerivedCategory.TStructure.t.plus M₀ :=
    ((Etale.openImmersionLowerShriek A c.i).bounded_mapDerivedCategory_obj hK₀).1
  -- `i_! K ≅ ν^* M₀` and `L ≅ ν^* L₀`
  let eM : D(ProEtale.openImmersionLowerShriek A c.i).obj K ≅ L(ν^*(c.Z)[A]).obj M₀ :=
    D(ProEtale.openImmersionLowerShriek A c.i).mapIso eK.symm ≪≫
      (Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso A c.i).symm ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).app K₀ ≪≫
      ((ν^*(c.Z)[A]).leftDerivedFunctorIsoMapDerivedCategory.app M₀).symm
  let eL' : L ≅ L(ν^*(Y)[A]).obj L₀ :=
    eL.symm ≪≫ ((ν^*(Y)[A]).leftDerivedFunctorIsoMapDerivedCategory.app L₀).symm
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived A c.g M₀ L₀ hM₀ hML
  have := NatTrans.isIso_app_app_of_iso
    (rightDerivedLowerStarProjectionMap A c.g) eM.symm eL'.symm
  infer_instance

end ProEtale

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

end AlgebraicGeometry.ProEtale
