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
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!

# Tor amplitude and internal hom under the pro-étale comparison

Let `ν : X_proét ⥤ X_ét` be the comparison morphism of sites and `ν^*` the induced exact functor
`D(X_ét) ⥤ D(X_proét)`. This file records how `ν^*` interacts with the finite Tor amplitude and
with the internal hom of bounded constructible complexes at a finite coefficient ring `Λ`.

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory`
  (`lem-sf-comparison-tor-amplitude` (ii)): an étale complex whose pullback to the pro-étale
  site is bounded constructible of Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`.
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
comparison, clause (ii).

Let `Λ` be a finite ring whose exponent is invertible on `X`, and let `K'` be a bounded below
complex of étale `Λ`-sheaves. If `ν^* K'` is bounded constructible on `X_proét` with Tor
amplitude in `[a, b]`, then `K'` has Tor amplitude in `[a, b]` on the étale site. -/
theorem torAmplitudeIn_of_mapDerivedCategory {X : Scheme.{u}} [HasInvertibleExponent Λ X]
    {a b : ℤ} {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : _root_.DerivedCategory.TStructure.t.plus K')
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K'))
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K')) :
    Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K' :=
  sorry

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
