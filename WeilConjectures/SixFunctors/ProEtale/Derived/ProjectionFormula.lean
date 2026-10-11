/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.FlatModuleCat

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

- `AlgebraicGeometry.ProEtale.hasProjectionFormula_of_constructibleFiniteTor`
  (`sk-thm-sf-pf-proetale`) : the projection formula for objects of `Dctf` at a finite
  coefficient ring `Λ`, and its version
  `AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_constructibleFiniteTor`
  for an arbitrary compactification.

## Implementation notes

The projection map is the composite of the projection map of `Rg_*` for the proper part `g` of
the compactification and of the inverse of the projection isomorphism for the open immersion
`i` (`AlgebraicGeometry.ProEtale.isIso_derivedOpenImmersionLowerShriekProjectionMap`); the
projection formula asserts that the former is an isomorphism on the relevant objects.

The blueprint's "étale-origin witnesses" for `K` and `L` are built into
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`, since pro-étale bounded
constructibility is defined as étale origin. For the same reason this notion agrees with the
blueprint's `Dctf(X_proét, A)` only at the finite coefficient stages `A = ModuleCat Λ`, `Λ` a
finite ring; the `𝒪_E`, `E` and `ℚ̄_ℓ` stages of `sk-thm-sf-pf-proetale` are not covered by
this statement.

As in the blueprint, the proof reduces to the étale projection formula along `ν^*`: the
comparison carries the étale projection map of `Rg_*` to the pro-étale one
(`WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison`), `ν^*` commutes
with extension by zero, and the étale projection formula for the proper `g` at finite
coefficients is `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`.
The finite Tor amplitude of `L` keeps `i_! K ⊗ᴸ Lg^* L` bounded below, where `ν^*` is known to
commute with `Rg_*`.

-/

@[expose] public section

universe u' u

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

variable {A} in
/-- Let `g : Z ⟶ Y`, let `M₀` and `L₀` be complexes of étale sheaves on `Z` and `Y` whose
pro-étale realizations `N ≅ ν^* M₀` and `L ≅ ν^* L₀` are respectively bounded and of finite Tor
amplitude. Then `M₀ ⊗ᴸ Lg^* L₀` is bounded below: its pro-étale realization is
`N ⊗ᴸ Lg^* L`, which is bounded since `Lg^* L` has finite Tor amplitude. -/
lemma plus_derivedTensor_leftDerivedUpperStar_of_comparison [Etale.UpperStarPreservesFlat A]
    [∀ X : Scheme.{u}, (ν^*(X)[A]).PreservesFlat] {Z : Scheme.{u}} (g : Z ⟶ Y)
    {M₀ : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    {L₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (eM : N ≅ L(ν^*(Z)[A]).obj M₀) (eL : L ≅ L(ν^*(Y)[A]).obj L₀)
    (hN : _root_.DerivedCategory.TStructure.t.bounded N) {a b : ℤ}
    (hL : DerivedCategory.torAmplitudeIn A Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀)) := by
  let P := (L(ProEtale.upperStar A g)).obj L
  obtain ⟨p, q, hNpq⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded N).2 hN
  have hPN := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left
    (torAmplitudeIn_leftDerivedUpperStar A g a b hL) hNpq
  obtain ⟨β⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (Scheme.ProEt.topology Z) A)
  let e : D(ν^*(Z)[A]).obj
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀)) ≅ P ⊗ N :=
    ((ν^*(Z)[A]).leftDerivedFunctorIsoMapDerivedCategory.app _).symm ≪≫
      asIso (((ν^*(Z)[A]).leftDerivedTensorComparison.app M₀).app _) ≪≫
      tensorIso eM.symm (((leftDerivedComparisonUpperStarCompUpperStarIso A g).app L₀).symm ≪≫
        (L(ProEtale.upperStar A g)).mapIso eL.symm) ≪≫
      @BraidedCategory.braiding _ _ _ β N P
  have hb : _root_.DerivedCategory.TStructure.t.bounded (D(ν^*(Z)[A]).obj
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀))) :=
    _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm
      ((_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1 ⟨_, _, hPN⟩)
  exact ((ν^*(Z)[A]).bounded_of_bounded_mapDerivedCategory_obj hb).1

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
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso A c.i).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _).app K₀ ≪≫
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

/-- The projection formula of `sk-thm-sf-pf-proetale` for `Rf_!` computed with an arbitrary
compactification `c` of `f`: for a finite ring `Λ` and `K`, `L` bounded constructible of finite Tor
amplitude, the projection map `PF_c : (Rf_!(c) K) ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^* L)` is an isomorphism.

Bounded constructibility on the pro-étale site is étale origin, so `K ≅ ν^* K₀` and
`L ≅ ν^* L₀` for étale complexes `K₀` and `L₀`. For the compactification `X ⟶[i] Z ⟶[g] Y` the
projection map is the one of `Rg_*` at `(i_! K, L)` followed by isomorphisms, and
`i_! ν^* K₀ ≅ ν^* i_! K₀`. The comparison `ν^*` carries the étale projection map of `Rg_*` to
the pro-étale one
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived`),
and the étale projection formula for the proper `g` at finite coefficients is
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`. The finite Tor
amplitude of `L` makes `i_! K₀ ⊗ᴸ Lg^* L₀` bounded below, where `ν^*` commutes with `Rg_*`. -/
theorem hasProjectionFormulaOfCompactification_of_constructibleFiniteTor [Finite Λ] {f : X ⟶ Y}
    (c : Compactification f)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    HasProjectionFormulaOfCompactification (ModuleCat.{u + 1} Λ) c K L := by
  obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := hK.1
  obtain ⟨L₀, -, ⟨eL⟩⟩ := hL.1
  obtain ⟨a, b, hLt⟩ := hL.2
  -- `i_! K₀ ⊗ᴸ Lg^* L₀` is bounded below, since its pro-étale realization `i_! K ⊗ᴸ Lg^* L` is
  have hML := plus_derivedTensor_leftDerivedUpperStar_of_comparison c.g
    (D(ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapIso eK.symm ≪≫
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) c.i).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _).app K₀ ≪≫
      ((ν^*(c.Z)[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.app _).symm)
    (eL.symm ≪≫
      ((ν^*(Y)[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.app L₀).symm)
    ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).bounded_mapDerivedCategory_obj
      hK.1.bounded) hLt
  -- the étale projection formula for the proper `g`
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite Λ c.g
  exact hasProjectionFormulaOfCompactification_of_comparison c eK eL hK₀.1 hML inferInstance

/-- Blueprint `sk-thm-sf-pf-proetale`: Projection formula: the pro-étale realization.

Let `Λ` be a finite ring (a finite coefficient stage). For a morphism `f : X ⟶ Y` admitting a
compactification, and `K` in `Dctf(X_proét, Λ)` and `L` in `Dctf(Y_proét, Λ)`, the projection
map `(Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)` is an isomorphism in `D(Y_proét)`. This is
`AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_constructibleFiniteTor`
for the chosen compactification of `f`. -/
theorem hasProjectionFormula_of_constructibleFiniteTor [Finite Λ] (f : X ⟶ Y)
    [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    HasProjectionFormula (ModuleCat.{u + 1} Λ) f K L :=
  hasProjectionFormulaOfCompactification_of_constructibleFiniteTor Λ
    (HasCompactification.compactification f) hK hL

end AlgebraicGeometry.ProEtale
