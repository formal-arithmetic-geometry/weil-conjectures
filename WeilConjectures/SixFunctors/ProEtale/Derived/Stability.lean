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
for `Y` of finite type over a field `k`, `A` killed by an integer `N` invertible in `k`, and
`f : X ⟶ Y` separated of finite type, the derived direct image
`Rf_* : D(X_proét) ⥤ D(Y_proét)` preserves bounded constructibility, and if `dim X ≤ d` it
moves the Tor amplitude from `[a, b]` to `[a, b + 2d]`.

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
origin. This route also needs comparison results for `ν^*` that the repository does not have
yet: `Rf_* ∘ D(ν^*) ≅ D(ν^*) ∘ Rf_*`, and that `D(ν^*)` preserves and reflects Tor amplitude.

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

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

namespace ProEtale

section DirectImage

variable [hA' : ConcreteCategory.FinitelyGeneratedOfMono A]
  {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0) (hA : ∀ M : A, N • 𝟙 M = 0)
  {X Y : Scheme.{u}} (s : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
  (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

include hN hA hA' s

/-- Blueprint `sk-cor-sf-direct-image-ctf`: Direct image preserves bounded constructibility on
the pro-étale site.

Let `Y` be of finite type over a field `k`, let `A` be killed by an integer `N` invertible in
`k` and noetherian, subobjects of finitely generated objects being finitely generated
(`CategoryTheory.ConcreteCategory.FinitelyGeneratedOfMono`, which holds for `ModuleCat Λ` with
`Λ` noetherian), and let `f : X ⟶ Y` be separated of finite type. If `K` is a bounded
constructible complex on `X_proét`, then `Rf_* K` is bounded constructible on `Y_proét`. -/
theorem boundedConstructible_rightDerivedLowerStar
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hbc : DerivedCategory.boundedConstructible A X K) :
    DerivedCategory.boundedConstructible A Y ((R((f)_*[A])).obj K) :=
  sorry

/-- Blueprint `sk-cor-sf-direct-image-ctf`: Tor amplitude of the pro-étale direct image.

In the situation of `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`,
if `dim X ≤ d` and `K` has Tor amplitude in `[a, b]`, then `Rf_* K` has Tor amplitude in
`[a, b + 2d]`. The shift `2d` is the uniform vanishing of `Rᵖf_*` above twice the dimension of
the source, for torsion coefficients of order invertible on the base. -/
theorem torAmplitudeIn_rightDerivedLowerStar (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hbc : DerivedCategory.boundedConstructible A X K)
    (hta : DerivedCategory.torAmplitudeIn A X a b K) :
    DerivedCategory.torAmplitudeIn A Y a (b + 2 * (d : ℤ)) ((R((f)_*[A])).obj K) :=
  sorry

end DirectImage

end ProEtale

end AlgebraicGeometry
