/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory

/-!

# Tor amplitude and internal hom under the pro-étale comparison

Let `ν : X_proét ⥤ X_ét` be the comparison morphism of sites and `ν^*` the induced exact functor
`D(X_ét) ⥤ D(X_proét)`. This file records how `ν^*` interacts with the finite Tor amplitude and
with the internal hom of bounded constructible complexes at a finite coefficient ring `Λ`.

## Main statements

- `AlgebraicGeometry.ProEtale.monoidal_comparisonUpperStar`: `ν^*` is strong monoidal on sheaves
  of `Λ`-modules.
- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`
  (`lem-exc-comparison-tor-interval`): an étale complex has Tor amplitude in `[a, b]` if and only
  if its pullback to the pro-étale site has.
- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory`
  (`lem-sf-comparison-tor-amplitude` (ii)): an étale complex whose pullback to the pro-étale
  site has Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom`
  (`thm-sf-hom-comparison-constructible`): `ν^* RHom(K, M) ≅ RHom(ν^* K, ν^* M)` for `K` in
  `Dctf(X_ét, Λ)` and `M` in `Dᵇc(X_ét, Λ)`, on a finite-type scheme over `k = F̄_p`.

## Implementation notes

The canonical comparison map `ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` needs a monoidal structure
on the derived `ν^*`, which is not formalised; the comparison is therefore stated as the
existence of an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

set_option synthInstance.maxHeartbeats 400000 in
-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small étale and
-- pro-étale sites take long to synthesize
/-- The comparison functor `ν^* : Sh(X_ét, Λ) ⥤ Sh(X_proét, Λ)` is strong monoidal. This is
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackMonoidal` for the inclusion of the
small étale site into the small pro-étale site, whose comma categories are filtered. -/
noncomputable instance monoidal_comparisonUpperStar (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) : ν^*(X)[ModuleCat.{u + 1} Λ].Monoidal :=
  have (K : X.ProEtᵒᵖ) : IsFiltered (CostructuredArrow (X.toProEt).op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ (Opposite.unop K))
  inferInstanceAs (Functor.sheafPullbackConstruction.sheafPullback (X.toProEt)
    (ModuleCat.{u + 1} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)).Monoidal

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- The derived comparison pullback `ν^*` sends the monoidal unit `Λ_{X_ét}` of `D(X_ét)` to
the monoidal unit `Λ_X` of `D(X_proét)`. -/
noncomputable def mapDerivedCategoryComparisonUpperStarUnitIso (X : Scheme.{u}) :
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ≅ 𝟙_ _ :=
  D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (comparisonUpperStarUnitIso Λ X) ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso _

/-- Blueprint `lem-sf-comparison-tor-amplitude`: Finite Tor amplitude under the site
comparison, clause (i).

Let `Λ` be a finite ring. If a complex `K'` of étale `Λ`-sheaves has Tor amplitude in
`[a, b]`, then `ν^* K'` has Tor amplitude in `[a, b]` on the pro-étale site: a flat model of
`K'` in degrees `[a, b]` is carried by the exact functor `ν^*` to a flat model of `ν^* K'`, as
`ν^*` preserves flat sheaves (`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`). The
blueprint's hypotheses that `K'` be bounded constructible and that the exponent of `Λ` be
invertible on `X` are not needed. -/
theorem torAmplitudeIn_mapDerivedCategory {X : Scheme.{u}}
    {a b : ℤ} {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hKt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K') :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K') :=
  _root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj _
    (fun _ ↦ flat_comparisonUpperStar_obj) hKt

/-- Blueprint `lem-sf-comparison-tor-amplitude`: Finite Tor amplitude under the site
comparison, clause (i).

The derived comparison pullback `ν^*` carries `Dctf(X_ét, Λ)` into `Dctf(X_proét, Λ)`, for a
finite ring `Λ`. -/
theorem constructibleFiniteTor_mapDerivedCategory {X : Scheme.{u}}
    {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K') :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K') :=
  have ⟨hbc, a, b, hKt⟩ := hK'
  ⟨boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hbc, a, b,
    torAmplitudeIn_mapDerivedCategory Λ hKt⟩

variable {Λ} in
/-- Blueprint `lem-exc-comparison-tor-interval`: Site comparison preserves and detects Tor
intervals.

Let `Λ` be a finite ring and `K` a complex of étale sheaves of `Λ`-modules. Then `K` has Tor
amplitude in `[a, b]` if and only if its pullback `ν^* K` to the pro-étale site has. The
pullback is exact, faithful and strong monoidal, and it preserves flat sheaves
(`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`), so this is
`DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff`. The blueprint's hypothesis that `K`
be bounded below is not needed. -/
theorem torAmplitudeIn_mapDerivedCategory_iff {X : Scheme.{u}} (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) ↔
      Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K :=
  _root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff _
    (fun _ ↦ flat_comparisonUpperStar_obj) a b K

/-- Blueprint `lem-sf-comparison-tor-amplitude`: Finite Tor amplitude under the site
comparison, clause (ii).

Let `Λ` be a finite ring and `K'` a complex of étale `Λ`-sheaves. If `ν^* K'` has Tor
amplitude in `[a, b]` on `X_proét`, then `K'` has Tor amplitude in `[a, b]` on the étale site.
This is the reverse implication of `torAmplitudeIn_mapDerivedCategory_iff`; the blueprint's
hypotheses that `K'` be bounded below, that `ν^* K'` be bounded constructible and that the
exponent of `Λ` be invertible on `X` are not needed. -/
theorem torAmplitudeIn_of_mapDerivedCategory {X : Scheme.{u}}
    {a b : ℤ} {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K')) :
    Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K' :=
  (torAmplitudeIn_mapDerivedCategory_iff a b K').1 hKt

/-- Blueprint `thm-sf-hom-comparison-constructible`: Internal-Hom comparison for finite-Tor
constructible inputs.

Let `X` be a scheme of finite type over an algebraic closure `k` of `𝔽_p`, let `Λ` be a finite
ring whose exponent is invertible on `X`, let `K ∈ Dctf(X_ét, Λ)` and `M ∈ Dᵇc(X_ét, Λ)`. Then
`ν^* RHom(K, M) ≅ RHom(ν^* K, ν^* M)`. -/
theorem nonempty_iso_mapDerivedCategory_derivedHom {k : Type u} [Field k] {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
        (((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M) ≅
      ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
        (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)) :=
  sorry

end AlgebraicGeometry.ProEtale.DerivedCategory
