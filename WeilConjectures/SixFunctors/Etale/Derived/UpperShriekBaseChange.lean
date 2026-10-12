/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# The base-change exchange for the exceptional inverse image

For a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `f`, `f'` admitting compactifications and finite coefficients `Λ`, the compactly
supported base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). Its inverse has a mate
under the adjunctions `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`,

`Ex^! : Lg'^* Rf^! ⟶ Rf'^! Lg^*`,

the canonical comparison of blueprint `lem-pur-smb-extraordinary`: at `K` it is the transpose
along `Rf'_! ⊣ Rf'^!` of

`Rf'_! Lg'^* Rf^! K ≅ Lg^* Rf_! Rf^! K ⟶ Lg^* K`,

the inverse of `Ex_!` followed by `Lg^*` of the counit. For smooth `f` it is an isomorphism
(smooth base change for `R^!`, `sk-prop-cohsm` (c)); in general it is not.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`: `Ex^! : Lg'^* Rf^! ⟶ Rf'^! Lg^*`.

## Main statements

- `AlgebraicGeometry.Etale.map_rightDerivedUpperShriekBaseChangeMap_app_comp_counit`:
  the defining property of `Ex^!` as a mate.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y X' Y' : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [HasCompactification f]
  [HasCompactification f'] [QuasiCompact f']

/-- The **base-change exchange for `R^!`**: for a cartesian square `g' ≫ f = f' ≫ g`, the
natural transformation

`Ex^! : Lg'^* Rf^! ⟶ Rf'^! Lg^*`,

mate under `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!` of the inverse of the compactly supported base
change isomorphism `Ex_! : Lg^* Rf_! ≅ Rf'_! Lg'^*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`). This is the canonical
comparison of blueprint `lem-pur-smb-extraordinary`. -/
noncomputable def rightDerivedUpperShriekBaseChangeMap (sq : IsPullback g' f' f g) :
    R(f)^![ModuleCat.{u + 1} Λ] ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')^![ModuleCat.{u + 1} Λ] :=
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  mateEquiv (rightDerivedUpperShriekAdjunction _ f) (rightDerivedUpperShriekAdjunction _ f')
    (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))

/-- The defining property of the base-change exchange `Ex^!` as a mate: the composite
`Rf'_! Lg'^* Rf^! K ⟶ Rf'_! Rf'^! Lg^* K ⟶ Lg^* K` of `Rf'_! Ex^!` and the counit is the
inverse of `Ex_!` followed by `Lg^*` of the counit of `Rf_! ⊣ Rf^!`. -/
@[reassoc]
lemma map_rightDerivedUpperShriekBaseChangeMap_app_comp_counit
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
    (R(f')_![ModuleCat.{u + 1} Λ]).map ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K) ≫
        (rightDerivedUpperShriekAdjunction _ f').counit.app _ =
      (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)).app _ ≫
        (L((g)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekAdjunction _ f).counit.app K) :=
  mateEquiv_counit _ _ _ K

end Etale

end AlgebraicGeometry
