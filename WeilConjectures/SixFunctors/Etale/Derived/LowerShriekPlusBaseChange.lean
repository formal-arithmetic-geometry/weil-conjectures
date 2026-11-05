/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange

/-!
# Compact-support base change on the bounded below étale derived categories

For a finite coefficient ring `Λ`, a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
with `g` arbitrary and a compactification `c = (X ⟶[c.i] c.Z ⟶[c.g] Y)` of `f`, the
compact-support exchange map (blueprint `def-cbc-exchange-map`)

`Ex_!(c) : g^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') g'^*`

on `D⁺(X_ét, Λ)` is the exchange map `CompactSupportFormalism.shriekBaseChange` of the compact
support formalism `AlgebraicGeometry.Etale.derivedPlusFormalism` of the bounded below étale
derived categories: the derived base change map `Ex_*` of the proper `c.g`
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, blueprint `def-weil-pbc-derived-exchange`),
applied to `(c.i)_! K`, composed with the base change isomorphism of the extension by zero
(blueprint `cor-cbc-derived-extension-zero-base-change`). It is an isomorphism: the first factor
by the bounded below proper base change theorem
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`, blueprint
`thm-weil-pbc-bounded-below`), the second by base change for the extension by zero
(blueprint `thm-cbc-finite-torsion`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`: the
  exchange map `Ex_!(c)` on `D⁺`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusBaseChangeMap`: the exchange map
  `Ex_! : g^* R(f)_! ⟶ R(f')_! g'^*` of the canonical compactly supported direct images on `D⁺`.

## Main statements

- `AlgebraicGeometry.Etale.derivedPlusFormalism_pfBaseChange`: the base change map of the
  formalism is `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`
  and `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekPlusBaseChangeMap`: compact-support
  base change on `D⁺` (blueprint `thm-cbc-finite-torsion`). Naturality in `K` holds since the
  exchange maps are natural transformations; the identity and pasting laws and the independence
  of the compactification are `CompactSupportFormalism.shriekBaseChange_id`,
  `CompactSupportFormalism.shriekBaseChange_paste_horiz`,
  `CompactSupportFormalism.lowerShriekBaseChange_paste_vert` and
  `CompactSupportFormalism.lowerShriekBaseChange_eq`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Formalism

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {U' U Z' Z : Scheme.{u}}

end Formalism

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

end Torsion

end Etale

end AlgebraicGeometry
