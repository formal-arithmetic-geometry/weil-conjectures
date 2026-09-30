/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!

# Stability of `Dctf` under direct image on the pro-étale site

Let `A` be a monoidal Grothendieck abelian coefficient category. This file is the pro-étale
counterpart of the direct-image part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`:
for `f : X ⟶ Y` separated of finite type with `dim X ≤ d`, the derived direct image
`Rf_* : D(X_proét) ⥤ D(Y_proét)` carries `Dctf(X, A)` into `Dctf(Y, A)`, moving the Tor
amplitude from `[a, b]` to `[a, b + 2d]`.

## Main statements

- `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`,
  `AlgebraicGeometry.ProEtale.torAmplitudeIn_rightDerivedLowerStar`
  (`sk-cor-sf-direct-image-ctf`).

## Implementation notes

The blueprint deduces this corollary from its étale counterpart
`sk-thm-sf-direct-image-tor-amplitude` by writing a bounded constructible pro-étale complex as
`ν^* K'` for an étale complex `K'`. No such étale-origin hypothesis appears here: bounded
constructibility on the pro-étale site
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`) is *defined* as étale
origin.

A dimension bound `dim X ≤ d` is `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, as in the étale
file.

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

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

namespace ProEtale

/-- Blueprint `sk-cor-sf-direct-image-ctf`: The direct image cell on the pro-étale site.

Let `f : X ⟶ Y` be separated of finite type with `dim X ≤ d`, and let `K` be a bounded
constructible complex on `X_proét` of Tor amplitude in `[a, b]`. Then `Rf_* K` is bounded
constructible on `Y_proét`. No étale-origin hypothesis appears: bounded constructible
pro-étale complexes are by definition of étale origin. -/
theorem boundedConstructible_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hbc : DerivedCategory.boundedConstructible A X K)
    (hta : DerivedCategory.torAmplitudeIn A X a b K) :
    DerivedCategory.boundedConstructible A Y ((R((f)_*[A])).obj K) :=
  sorry

/-- Blueprint `sk-cor-sf-direct-image-ctf`: The direct image cell on the pro-étale site.

In the situation of `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`,
the direct image `Rf_* K` has Tor amplitude in `[a, b + 2d]`. No étale-origin hypothesis
appears: bounded constructible pro-étale complexes are by definition of étale origin. -/
theorem torAmplitudeIn_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hbc : DerivedCategory.boundedConstructible A X K)
    (hta : DerivedCategory.torAmplitudeIn A X a b K) :
    DerivedCategory.torAmplitudeIn A Y a (b + 2 * (d : ℤ)) ((R((f)_*[A])).obj K) :=
  sorry

end ProEtale

end AlgebraicGeometry
