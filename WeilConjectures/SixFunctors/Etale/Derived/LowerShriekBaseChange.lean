/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# The compactly supported base change map along a compactification

For a cartesian square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

and a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`, the base changed compactification
`c.ofIsPullback sq = (X' ⟶[i'] Z ×_Y Y' ⟶[p'] Y')` of `f'` sits in a diagram of two cartesian
squares

```
  X' --g'--> X
  |          |
  i'         i
  ↓          ↓
  Z' --g''-> Z
  |          |
  p'         p
  ↓          ↓
  Y' --g---> Y
```

with `g'' = pullback.fst c.g g`. Pasting the derived base change map `Ex_*` of the bottom square
with the base change isomorphism of the extension by zero for the top square gives the
compactly supported base change map `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*`, computed with `c` and its
base change.

## Main definitions

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso`: for a cartesian
  square of open immersions, the isomorphism `Lg''^* Dj_! ≅ Dj'_! Lg'^*` on unbounded derived
  categories.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`: the
  exchange map `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_iff`:
  `Ex_!(c)` is an isomorphism if and only if the derived base change map `Ex_*` of the bottom
  square of the diagram above, whiskered by `Di_!`, is.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap`:
  `Ex_!(c)` is an isomorphism if `Ex_*` of the bottom square is.

The top square is cartesian by `AlgebraicGeometry.Compactification.isPullback_ofIsPullback_i`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

section OpenImmersion

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **Derived base change for the extension by zero**: for a cartesian square
`g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the isomorphism
`Lg''^* Dj_! ≅ Dj'_! Lg'^*` on unbounded derived categories, induced by the inverse of the
base change isomorphism `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`
(both `g''^*` and `g'^*` being exact, their left derived functors are the induced functors). -/
noncomputable def derivedOpenImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'') :
    D((j)_!open[A]) ⋙ L((g'')^*[A]) ≅ L((g')^*[A]) ⋙ D((j')_!open[A]) :=
  have := isIso_openImmersionLowerShriekBaseChangeMap A hsq
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A g'') ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekBaseChangeMap A hsq.toCommSq)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g').symm _

end OpenImmersion

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **The compactly supported base change map along a compactification** `Ex_!(c)`: for a
cartesian square `g' ≫ f = f' ≫ g` and a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`, the
natural transformation `Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*`, where `c ×_Y Y'` is the base
changed compactification `c.ofIsPullback sq` of `f'`. It is the derived base change map `Ex_*`
of the cartesian square `Z ×_Y Y' ⟶ Z` over `g`, whiskered by `Di_!`, followed by the derived
base change isomorphism of the extension by zero for the cartesian square
`AlgebraicGeometry.Compactification.isPullback_ofIsPullback_i`, whiskered by `Rp'_*`.

```
  D(X) --Lg'^*--> D(X')
   |               |
  Di_!            Di'_!
   ↓               ↓
  D(Z) --Lg''^*-> D(Z')
   |               |
  Rp_*    ⇓ Ex_*  Rp'_*
   ↓               ↓
  D(Y) --Lg^*---> D(Y')
```

(blueprint: `sk-def-sf-exchanges`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    Rf_!(c)[A] ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ Rf_!(c.ofIsPullback sq)[A] :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open[A])
      (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g g).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionLowerShriekBaseChangeIso A (c.isPullback_ofIsPullback_i sq)).hom
      R(((c.ofIsPullback sq).g)_*[A]) ≫
    (Functor.associator _ _ _).hom

/-- `Ex_!(c)` is an isomorphism if and only if the derived base change map `Ex_*` of the
cartesian square `c.Z ×_Y Y' ⟶ c.Z` over `g`, whiskered by `Di_!`, is: the other factors of
`Ex_!(c)` are isomorphisms. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_iff
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c) ↔
      IsIso (Functor.whiskerLeft D((c.i)_!open[A])
        (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g g).toCommSq)) := by
  rw [rightDerivedLowerShriekOfCompactificationBaseChangeMap, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- If the derived base change map `Ex_*` of the cartesian square `c.Z ×_Y Y' ⟶ c.Z` over `g`
is an isomorphism, then so is `Ex_!(c)`. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f)
    [IsIso (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g g).toCommSq)] :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c) :=
  (isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_iff A sq c).2 inferInstance

end Etale

end AlgebraicGeometry
