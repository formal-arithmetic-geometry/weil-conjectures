/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions

/-!
# Dual base change for the exceptional inverse image

For a cartesian square of schemes
```
  X' --g'--> X
  | |
  f' f
  v v
  Y' --g---> Y
```
with `f`, `f'` admitting compactifications and torsion coefficients `Λ`, the compact-support
base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). Its conjugate under the
composite adjunctions `Lg^* Rf_! ⊣ Rf^! Rg_*` and `Rf'_! Lg'^* ⊣ Rg'_* Rf'^!` is the exchange
`Rg'_* Rf'^! ⟶ Rf^! Rg_*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeMap`), an isomorphism. Its
inverse is the *dual base change isomorphism*
```
  β^∨ : Rf^! Rg_* ≅ Rg'_* Rf'^!
```
Here the right adjoint `Rf^!` of `Rf_!` exists unconditionally
(`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDualBaseChangeIso`: `β^∨`.

## Implementation details

The pro-étale analogue is not stated: the pro-étale compact-support base change
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekBaseChangeMap` is only known to be invertible
on complexes of étale origin, not as a natural transformation of functors on the ambient
derived categories, so its conjugate is not known to be invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- Dual base change: for a cartesian square `g' ≫ f = f' ≫ g` with `f`, `f'` admitting
compactifications (and `f'` quasi-compact) and `g` arbitrary, and torsion coefficients `Λ`, the
isomorphism `β^∨ : Rf^! Rg_* ≅ Rg'_* Rf'^!` (written `Rg_* ⋙ Rf^! ≅ Rf'^! ⋙ Rg'_*`), the inverse
of the exchange isomorphism `AlgebraicGeometry.Etale.rightDerivedUpperShriekLowerStarBaseChangeMap`.
-/
noncomputable def rightDerivedUpperShriekDualBaseChangeIso (sq : IsPullback g' f' f g) :
    R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ R(f)^![Λ] ≅
      R(f')^![Λ] ⋙ R((g')_*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq
  (asIso (rightDerivedUpperShriekLowerStarBaseChangeMap Λ sq)).symm

end Etale

end AlgebraicGeometry
