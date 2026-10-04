/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Compact-support base change and the projection formula

The two theorems of the six-functor formalism attached to `Rf_!` that the purity chapter
consumes: compact-support base change for a cartesian square, and the projection formula.

## Implementation notes

Compact-support base change is stated as `IsIso Ex_!` for the exchange
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of the framework chapter's `sk-def-sf-exchanges`, which is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap` (and
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap` for a given
compactification). Its construction needs `f'` to be quasi-compact, so the statement assumes
`[QuasiCompact f']`. The projection map `PF : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)` is not
constructed yet, so the projection formula below asserts that the two objects in question are
isomorphic. It should be restated as `IsIso PF`, in the style of
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`.

The exchange `Ex_*` for `Rf_*` does already exist in this repository, as
`AlgebraicGeometry.Etale.baseChange` and `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_leftDerivedUpperStar`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

section Exchange

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f']

/-- Blueprint `sk-prop-sf-cbc`: Compact-support base change

**Compact-support base change.** For `f : X ⟶ Y` separated of finite type, `g : Y' ⟶ Y`
arbitrary and a cartesian square

```
  X' --g'--> X            Rf_! ⋙ Lg^*  --Ex_!-->  Lg'^* ⋙ Rf'_!
  |          |
  f'         f            as functors D(X_ét, Λ) ⥤ D(Y'_ét, Λ)
  |          |
  v          v
  Y' --g---> Y
```

the exchange transformation `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of `sk-def-sf-exchanges` is an
isomorphism.

The proof is the five-stage argument of the compact-support base change chapter: finite
coefficients on the étale site, degreewise constructibility, the pro-étale finite level for
objects with an étale-origin witness, completed coefficients, and finite extensions of the
coefficient field. -/
theorem isIso_rightDerivedLowerShriekBaseChangeMap [Finite Λ] [HasInvertibleExponent Λ Y]
    [LocallyOfFiniteType f] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq) :=
  sorry

end Exchange

section Projection

variable (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `sk-thm-sf-pf-finite`: Projection formula, finite coefficients

**The projection formula at finite coefficients.** For `Λ` a finite coefficient ring whose
exponent is invertible on `Y`, `f : X ⟶ Y` separated of finite type, `K` bounded constructible
on `X` and `L` bounded constructible *of finite Tor amplitude* on `Y`, the projection map

`PF : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)`

is an isomorphism, naturally in `K` and `L`. The finite Tor amplitude of `L` is essential: the
fibrewise argument represents the stalks of `L` by bounded complexes of finite free modules. -/
-- TODO(unify): def:exchange-projection — restate as `IsIso (PF f K L)`.
theorem nonempty_iso_derivedTensor_rightDerivedLowerShriek [Finite Λ]
    [HasInvertibleExponent Λ Y] [LocallyOfFiniteType f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.boundedConstructibleFiniteTor Λ Y L) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj L ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L))) :=
  sorry

/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

**`Rf_!` commutes with finite reduction.** For an ideal `J` of `Λ`,

`Rf_!(K ⊗^L (Λ/J)_X) ≅ (Rf_! K) ⊗^L (Λ/J)_Y`.

This is one of the three compatibilities out of which the comparison square of
`sk-prop-sf-pf-reduction` is built, and the only one that is not formal; it is what reduces
the projection formula at level `n` to the projection formula at level `m ≤ n`. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriek (J : Ideal Λ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ]) :=
  sorry

/-- Blueprint `sk-prop-sf-pf-reduction`: Projection formula: compatibility with finite
reduction

**`Lf^*` commutes with finite reduction.** For an ideal `J` of `Λ`,

`Lf^*(L ⊗^L (Λ/J)_Y) ≅ (Lf^* L) ⊗^L (Λ/J)_X`,

because `Lf^*` is monoidal and carries the constant complex on `Λ/J` to the constant complex
on `Λ/J`. Together with the associativity of `⊗^L` and
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek` this is what
makes the comparison square of the blueprint commute. -/
theorem nonempty_iso_reductionModIdeal_leftDerivedUpperStar (J : Ideal Λ) :
    Nonempty (reductionModIdeal Λ Y J ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ≅
      L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ X J) :=
  sorry

end Projection

end Etale

end AlgebraicGeometry
