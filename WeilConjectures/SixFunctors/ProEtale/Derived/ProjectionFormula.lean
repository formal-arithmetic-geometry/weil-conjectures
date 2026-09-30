/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!

# The projection formula on the pro-étale site

Let `A` be a monoidal Grothendieck abelian coefficient category and let `f : X ⟶ Y` be a
morphism of schemes admitting a compactification, so that the compactly supported direct
image `Rf_! : D(X_proét) ⥤ D(Y_proét)` is available. The *projection formula* is the assertion
that the canonical comparison map

```
  PF_{f, K, L} : Rf_!(K ⊗ᴸ Lf^* L) ⟶ (Rf_! K) ⊗ᴸ L
```

is an isomorphism, for `K : D(X_proét)` and `L : D(Y_proét)`. This file is the pro-étale
counterpart of `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`.

## Main definitions

- `AlgebraicGeometry.ProEtale.HasProjectionFormulaOfCompactification` : the projection formula
  for `Rf_!` computed with a given compactification `c` of `f`.
- `AlgebraicGeometry.ProEtale.HasProjectionFormula` : the projection formula for `Rf_!`
  computed with the chosen compactification `HasCompactification.compactification f`.

## Main statements

- `AlgebraicGeometry.ProEtale.hasProjectionFormula_of_constructibleFiniteTor`
  (`sk-thm-sf-pf-proetale`) : the projection formula for objects of `Dctf`.

## Implementation notes

The canonical map `PF_{f, K, L}` is not available in this repository, so, as on the étale
side, the projection formula is recorded as the `Prop`-valued property
`AlgebraicGeometry.ProEtale.HasProjectionFormula` asserting that the two objects are
*isomorphic*. This is a placeholder: it should become the statement that the canonical map is an
isomorphism, which is also what is needed to compare the formula with the étale one along `ν^*`.

The blueprint's "étale-origin witnesses" for `K` and `L` are built into
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`, since pro-étale bounded
constructibility is defined as étale origin. For the same reason this notion agrees with the
blueprint's `Dctf(X_proét, A)` only at the finite coefficient stages; the `𝒪_E`, `E` and
`ℚ̄_ℓ` stages of `sk-thm-sf-pf-proetale` are not covered by this statement. Accordingly the
coefficient category is assumed torsion: `N • 𝟙 M = 0` for some `N ≠ 0` and every `M : A`.
At these stages the torsion projection formula (SGA 4 XVII 5.2.9) holds without the finite Tor
amplitude assumption; it is kept to match the blueprint's `Dctf` statement.

The blueprint proves this by reduction to the étale torsion projection formula along `ν^*`. That
needs the étale torsion projection formula and the compatibility of `D(ν^*)` with `Rf_!`, `Lf^*`
and `⊗ᴸ`, none of which is in the repository yet.

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

/-- The projection formula for a morphism `f : X ⟶ Y`, at `K : D(X_proét)` and
`L : D(Y_proét)`, with `Rf_!` computed from a chosen compactification `c` of `f`: the assertion
that

```
  Rf_!(K ⊗ᴸ Lf^* L)  ≅  (Rf_! K) ⊗ᴸ L .
```

The canonical comparison map going from left to right is not constructed in this
repository, so the property records the existence of *some* isomorphism between the two
objects; see the module docstring. -/
def HasProjectionFormulaOfCompactification {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) : Prop :=
  Nonempty ((Rf_!(c)[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj ((L((f)^*[A])).obj L)) ≅
    ((-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K)).obj L)

/-- The projection formula for a morphism `f : X ⟶ Y` admitting a compactification, at
`K : D(X_proét)` and `L : D(Y_proét)`: the assertion that

```
  Rf_!(K ⊗ᴸ Lf^* L)  ≅  (Rf_! K) ⊗ᴸ L ,
```

with `Rf_!` the compactly supported direct image
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriek` attached to the chosen compactification
of `f`. -/
def HasProjectionFormula (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) : Prop :=
  HasProjectionFormulaOfCompactification A (HasCompactification.compactification f) K L

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Blueprint `sk-thm-sf-pf-proetale`: Projection formula: the pro-étale realization.

Let `A` be killed by an integer `N ≠ 0`. For a morphism `f : X ⟶ Y` admitting a
compactification, and `K` in `Dctf(X_proét, A)` and `L` in `Dctf(Y_proét, A)`, there is an
isomorphism `Rf_!(K ⊗ᴸ Lf^* L) ≅ (Rf_! K) ⊗ᴸ L` in `D(Y_proét)`. -/
theorem hasProjectionFormula_of_constructibleFiniteTor (N : ℕ) (hN : N ≠ 0)
    (hA : ∀ M : A, N • 𝟙 M = 0) (f : X ⟶ Y) [HasCompactification f]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hL : DerivedCategory.constructibleFiniteTor A Y L) :
    HasProjectionFormula A f K L :=
  sorry

end ProEtale

end AlgebraicGeometry
