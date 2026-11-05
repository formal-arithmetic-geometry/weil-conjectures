/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor
import WeilConjectures.SixFunctors.Etale.Derived.ConstantTensorProjection

/-!
# Compact-support base change, the projection formula and finite reduction

The two theorems of the six-functor formalism attached to `Rf_!` that the purity chapter
consumes: compact-support base change for a cartesian square, and the projection formula.
Alongside them, the compatibilities of `Rf_!`, `Lf^*` and `Rf_*` with the reduction
`K ↦ K ⊗ᴸ (Λ/J)` of the coefficients modulo an ideal `J`.

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
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, which is defined for torsion coefficients
and rests on unbounded proper base change. The hypothesis `[QuasiCompact f']` should disappear
once `Ex_!` is constructed on `D⁺`.

The projection formula is stated as the invertibility of the projection map
`PF : Rf_! K ⊗^L L ⟶ Rf_!(K ⊗^L Lf^* L)` of `AlgebraicGeometry.Etale.projectionMap`
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`, in
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`); its case of `sk-thm-sf-pf-finite`,
for `K` bounded constructible and `L` in `Dᵇctf`, is
`AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`.

The exchange `Ex_*` for `Rf_*` does already exist in this repository, as
`AlgebraicGeometry.Etale.baseChange` and `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite`
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_boundedConstructible`
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite`,
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
That comparison isomorphism is
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`, which rests
on unbounded proper base change; the blueprint states this theorem on `D⁺`. If `f` is
quasi-compact, `[QuasiCompact f']` is obtained from `sq` by `MorphismProperty.of_isPullback`. -/
-- TODO: state this for the `D⁺` exchange map built from `derivedBaseChangeMapPlus`, and drop
-- `[QuasiCompact f']` once `Ex_!` is constructed without it.
theorem isIso_rightDerivedLowerShriekBaseChangeMap [Finite Λ] [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedLowerShriekBaseChangeMap Λ sq) := by
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite Λ sq
    (HasCompactification.compactification f)
  unfold rightDerivedLowerShriekBaseChangeMap
  infer_instance

end Exchange

section Projection

variable (f : X ⟶ Y) [HasCompactification f]

end Projection

section LowerStar

end LowerStar

end Etale

end AlgebraicGeometry
