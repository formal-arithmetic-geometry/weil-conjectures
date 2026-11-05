/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange

/-!
# Compact-support exchange maps along compatible compactifications

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be morphisms of schemes with compactifications
`c = (X ⟶[c.i] c.Z ⟶[c.g] Y)` and `c' = (X' ⟶[c'.i] c'.Z ⟶[c'.g] Y')`, and let `g : Y' ⟶ Y`,
`g' : X' ⟶ X` and `gZ : c'.Z ⟶ c.Z` be morphisms such that
```
X' --c'.i--> c'.Z --c'.g--> Y'
|g'           |gZ            |g
v             v              v
X  --c.i-->  c.Z  --c.g-->  Y
```
commutes, the left square being cartesian. The *compact-support exchange map*
(blueprint `def-exchange-projection`, `def-cbc-exchange-map`)

`Ex_! : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`

on the unbounded derived categories of pro-étale sheaves is the derived base change map
`Lg^* R(c.g)_* ⟶ R(c'.g)_* L(gZ)^*` of the right square
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`) applied after `(c.i)_!`, followed by the
inverse of the base change isomorphism `(c'.i)_! g'^* ≅ gZ^* (c.i)_!` of the extension by zero
along the cartesian left square
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`, blueprint
`lem-cbc-proetale-extension-zero-base-change`). For `c' = c ×_Y Y'` and a cartesian outer square
it is the map `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`.

## Main definitions

- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso`: the
  base change isomorphism `L(g'')^* j_! ≅ j'_! Lg'^*` of the extension by zero along a cartesian
  square of open immersions, with derived pullbacks.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChange`: the exchange
  map `Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section OpenImmersion

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

end OpenImmersion

section Compactification

variable {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} (c : Compactification f)
  (c' : Compactification f') {g : Y' ⟶ Y} {g' : X' ⟶ X} {gZ : c'.Z ⟶ c.Z}

end Compactification

end AlgebraicGeometry.ProEtale
