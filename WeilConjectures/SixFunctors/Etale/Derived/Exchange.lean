/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange

/-!
# Compact-support base change and the projection formula

The two theorems of the six-functor formalism attached to `Rf_!` that the purity chapter
consumes: compact-support base change for a cartesian square, and the projection formula.

## Implementation notes

Compact-support base change is stated as `IsIso Ex_!` for the exchange
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of the framework chapter's `sk-def-sf-exchanges`, on the
unbounded derived categories. The main form is for the exchange map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap` computed with
an arbitrary compactification `c` of `f`: it reduces to unbounded proper base change for the
proper map of `c`. The blueprint states it on `D⁺` instead.

The statement for the canonical exchange map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap` is a corollary. That map is only
defined for `f'` quasi-compact, and it goes through the comparison isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, which rests on an unproved instance that is
not expected to hold on unbounded derived categories in this generality. Both the hypothesis
`[QuasiCompact f']` and this dependence should disappear once `Ex_!` is constructed on `D⁺`.

The projection map `PF : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)` is not
constructed yet, so the projection formula below asserts that the two objects in question are
isomorphic. It should be restated as `IsIso PF`, in the style of
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`.

The exchange `Ex_*` for `Rf_*` does already exist in this repository, as
`AlgebraicGeometry.Etale.baseChange` and `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`
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

/-- **Compact-support base change along a compactification.** For a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `g` arbitrary, a compactification `c` of `f` and `Λ` finite, the exchange transformation
`Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*` of `sk-def-sf-exchanges`, computed with `c`
and its base change, is an isomorphism of functors `D(X_ét, Λ) ⥤ D(Y'_ét, Λ)`.

This is the blueprint's raw finite compact-support base change theorem, stated on the
unbounded derived categories rather than on `D⁺`. By
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap` it
reduces to the invertibility of the derived base change map `Ex_*` for the proper map `c.g`,
which is unbounded proper base change
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite [Finite Λ]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c) :=
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
    (IsPullback.of_hasPullback c.g g)
  isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c

/-- Blueprint `sk-prop-sf-cbc`: Compact-support base change

**Compact-support base change.** For `f : X ⟶ Y` admitting a compactification, `g : Y' ⟶ Y`
arbitrary, a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `f'` quasi-compact and admitting a compactification, and `Λ` finite, the exchange
transformation `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` of `sk-def-sf-exchanges` is an isomorphism of
functors `D(X_ét, Λ) ⥤ D(Y'_ét, Λ)`.

`Ex_!` is `Ex_!(c)` for the chosen compactification `c` of `f`, followed by the comparison
isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso` for `f'`, so this follows from
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`.
That comparison isomorphism rests on the unproved instance
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`, which is not
expected to hold on unbounded derived categories in this generality; the blueprint states this
theorem on `D⁺`. If `f` is quasi-compact, `[QuasiCompact f']` is obtained from `sq` by
`MorphismProperty.of_isPullback`. -/
-- TODO: state this for the `D⁺` exchange map built from `derivedBaseChangeMapPlus`, and drop
-- `[QuasiCompact f']` once `Ex_!` is constructed without it.
theorem isIso_rightDerivedLowerShriekBaseChangeMap [Finite Λ] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq) := by
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite Λ sq
    (HasCompactification.compactification f)
  unfold rightDerivedLowerShriekBaseChangeMap
  infer_instance

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

section LowerStar

variable (f : X ⟶ Y)

/-- **`Rf_*` commutes with finite reduction.** For an ideal `J` of the finite coefficient ring
`Λ` and `f` quasi-compact, quasi-separated and locally of finite type, with the exponent of
`Λ` invertible on `Y`,

`(Rf_* K) ⊗^L (Λ/J)_Y ≅ Rf_*(K ⊗^L (Λ/J)_X)`.

This is the projection formula of `Rf_*` for the constant complex `(Λ/J)_Y`, whose pullback is
`(Λ/J)_X`. It holds for every `K` because `Rf_*` has finite cohomological dimension under
these hypotheses, so that it commutes with the tensor product with the terms of a resolution
of `Λ/J` by finite free `Λ`-modules and with the colimit of their truncations. It is the
ordinary counterpart of
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerStar [Finite Λ]
    [HasInvertibleExponent Λ Y] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (J : Ideal Λ) :
    Nonempty (R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) :=
  sorry

end LowerStar

end Etale

end AlgebraicGeometry
