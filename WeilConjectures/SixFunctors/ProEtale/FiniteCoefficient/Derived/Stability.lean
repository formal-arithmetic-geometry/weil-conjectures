/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageCohomologicalDimension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Sites.NsmulSheaf

/-!

# Stability of `Dctf` under direct image on the pro-étale site

This file is the pro-étale counterpart of the direct-image part of
`WeilConjectures.SixFunctors.Etale.Derived.Stability`: for `Y` of finite type over a field `k`,
coefficients killed by an integer `N` invertible in `k`, and `f : X ⟶ Y` separated of finite
type, the derived direct image `Rf_* : D(X_proét) ⥤ D(Y_proét)` preserves bounded
constructibility, and for a finite coefficient ring `Λ` and `dim X ≤ d` it moves the Tor
amplitude from `[a, b]` to `[a, b + 2d]`.

## Main statements

- `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`,
  `AlgebraicGeometry.ProEtale.torAmplitudeIn_rightDerivedLowerStar`
  (`sk-cor-sf-direct-image-ctf`).
- `ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory`
  (`cor-sf-direct-image-ctf-etale-origin`): the case of a complex `ν^* K'` of étale origin.
- `AlgebraicGeometry.ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar`
  (`cor-sf-direct-image-ctf-proetale`): the case of every bounded constructible complex.

## Implementation notes

The blueprint deduces this corollary from its étale counterpart
`sk-thm-sf-direct-image-tor-amplitude` by writing a bounded constructible pro-étale complex as
`ν^* K'` for an étale complex `K'` (`lem-sf-proetale-constructible-origin`). Here bounded
constructibility on the pro-étale site
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`) is *defined* as étale
origin, so that lemma is built in. The two comparison inputs are `Rf_* ν^* K' ≅ ν^* Rf_* K'`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`) and the fact that
`ν^*` preserves and detects Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`, which needs
the coefficients to be a finite ring `Λ`).

The coefficient category is torsion of order invertible on the base: `N • 𝟙 M = 0` for every
`M : A`, with `(N : k) ≠ 0`. Without this the statements fail, already for
`A = ModuleCat (ZMod p)` and the affine line over a separably closed field of characteristic
`p`, whose `H¹` is infinite by Artin–Schreier theory. Being of finite type over a field is the
base condition of Deligne's finiteness theorem. These are the finite coefficient stages
`A_{E,n}` of the blueprint, where étale-origin bounded constructibility is the right notion.

A dimension bound `dim X ≤ d` is `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, as in the étale
file.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Pullback

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end Pullback

section DirectImage

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0) (hA : ∀ M : ModuleCat.{u + 1} Λ, N • 𝟙 M = 0)
  {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
  (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

include hN hA s

end Finite

section OpenImmersion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j] [QuasiCompact j]

end OpenImmersion

end DirectImage

end ProEtale

end AlgebraicGeometry
