/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek

/-!
# The exchange transformations on the pro-étale site

For a cartesian square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

blueprint `def-exchange-projection` defines the direct-image exchange
`Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*`, adjoint to `Lf'^* Lg^* Rf_* ≅ Lg'^* Lf^* Rf_* ⟶ Lg'^*`; this
is `AlgebraicGeometry.ProEtale.derivedBaseChangeMap`. For a compactification
`f = f̄ ∘ j`, the compact-support exchange `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` is `Ex_*` for `f̄`
followed by the canonical identification `Lḡ'^* j_! ≅ j'_! Lg'^*`. This file constructs that
identification on the small pro-étale sites, and `Ex_!`.

The identification is the inverse of the base change map `j'_! g'^* ⟶ ḡ'^* j_!`, the conjugate
of the weakly étale base change map `ProEtale.baseChangeMap` of the pushforward, which is an
isomorphism for a cartesian square (`AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback`).
This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`,
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange` and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange`.

## Main definitions

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekBaseChangeMap`: the base change map
  `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*` on pro-étale sheaves, an isomorphism for a cartesian square.
- `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`: the induced
  isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`: the
  compact-support exchange `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section OpenImmersion

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The base change map for the extension by zero on the small pro-étale sites: for a
commutative square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the
natural transformation `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*`, i.e. `j'_! g'^* ⟶ g''^* j_!`, conjugate
under `j_! ⋙ g''^* ⊣ g''_* ⋙ j^*` and `g'^* ⋙ j'_! ⊣ j'^* ⋙ g'_*` to the weakly étale base
change map `ProEtale.baseChangeMap : g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*`. -/
noncomputable def openImmersionLowerShriekBaseChangeMap (sq : CommSq g' j' j g'') :
    (g')^*[A] ⋙ (j')_!open[A] ⟶ (j)_!open[A] ⋙ (g'')^*[A] :=
  (conjugateEquiv ((ProEtale.openImmersionLowerShriekUpperStarAdjunction A j).comp
      (ProEtale.upperStarLowerStarAdjunction A g''))
    ((ProEtale.upperStarLowerStarAdjunction A g').comp
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction A j'))).symm
    (ProEtale.baseChangeMap A sq)

/-- **Base change for the extension by zero along a cartesian square** on the small pro-étale
sites: the base change map `j'_! g'^* ⟶ g''^* j_!` is an isomorphism. -/
lemma isIso_openImmersionLowerShriekBaseChangeMap (hsq : IsPullback g' j' j g'') :
    IsIso (openImmersionLowerShriekBaseChangeMap A hsq.toCommSq) :=
  have := ProEtale.isIso_baseChangeMap_of_isPullback A hsq
  conjugateEquiv_symm_iso _ _ _

/-- **Derived base change for the extension by zero**: for a cartesian square
`g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, the isomorphism
`Dg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Dg''^*` induced on the unbounded derived categories of pro-étale
sheaves by `openImmersionLowerShriekBaseChangeMap`. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
    (hsq : IsPullback g' j' j g'') :
    D((g')^*[A]) ⋙ D((j')_!open[A]) ≅ D((j)_!open[A]) ⋙ D((g'')^*[A]) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A hsq))
      ≪≫ Functor.mapDerivedCategoryCompIso _ _

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- **Derived base change for the extension by zero**, with derived pullbacks: the isomorphism
`Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` on the unbounded derived categories of pro-étale sheaves, for a
cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions. Its inverse is the
canonical identification `Lḡ'^* j_! ≅ j'_! Lg'^*` of blueprint `def-exchange-projection`. -/
noncomputable def derivedOpenImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'') :
    L((g')^*[A]) ⋙ D((j')_!open[A]) ≅ D((j)_!open[A]) ⋙ L((g'')^*[A]) :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g') _ ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A g'').symm

end OpenImmersion

section LowerShriek

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Blueprint `def-exchange-projection`: Exchange and projection transformations, the
compact-support exchange.

For a cartesian square `g' ≫ f = f' ≫ g` and a compactification `c = (X ⟶[j] X̄ ⟶[f̄] Y)` of
`f`, the compact-support exchange map `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c ×_Y Y') Lg'^*` on the
unbounded derived categories of pro-étale sheaves, computed with `c` and its base change
`c ×_Y Y' = (X' ⟶[j'] X̄' ⟶[f̄'] Y')` (`Compactification.ofIsPullback`): the direct-image exchange
`Ex_*` (`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`) for `f̄`, whiskered by `Dj_!`,
followed by the canonical identification `Lḡ'^* j_! ≅ j'_! Lg'^*`
(the inverse of `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`),
whiskered by `Rf̄'_*`.

```
  D(X) --Lg'^*--> D(X')
   |               |
  Dj_!     ≅     Dj'_!
   ↓               ↓
  D(X̄) --Lḡ'^*-> D(X̄')
   |               |
  Rf̄_*    ⇓ Ex_*  Rf̄'_*
   ↓               ↓
  D(Y) --Lg^*---> D(Y')
```
-/
noncomputable def rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    ProEtale.rightDerivedLowerShriekOfCompactification A c ⋙ L((g)^*[A]) ⟶
      L((g')^*[A]) ⋙ ProEtale.rightDerivedLowerShriekOfCompactification A (c.ofIsPullback sq) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((c.i)_!open[A])
      (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g g).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (derivedOpenImmersionLowerShriekBaseChangeIso A (c.isPullback_i_ofIsPullback sq)).inv
      R(((c.ofIsPullback sq).g)_*[A]) ≫
    (Functor.associator _ _ _).hom

/-- `Ex_!(c)` is an isomorphism if and only if `Ex_*` for the proper part of `c`, whiskered by
`Dj_!`, is one: the other factors are isomorphisms. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_iff
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    IsIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c) ↔
      IsIso (Functor.whiskerLeft D((c.i)_!open[A])
        (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g g).toCommSq)) := by
  simp only [rightDerivedLowerShriekOfCompactificationBaseChangeMap, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- The compact-support exchange `Ex_! : Lg^* Rf_! ⟶ Rf'_!(c ×_Y Y') Lg'^*` for the chosen
compactification `c` of `f`. -/
noncomputable def rightDerivedLowerShriekBaseChangeMap [HasCompactification f]
    (sq : IsPullback g' f' f g) :
    ProEtale.rightDerivedLowerShriek A f ⋙ L((g)^*[A]) ⟶
      L((g')^*[A]) ⋙ ProEtale.rightDerivedLowerShriekOfCompactification A
        ((HasCompactification.compactification f).ofIsPullback sq) :=
  rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq
    (HasCompactification.compactification f)

end LowerShriek

end ProEtale

end AlgebraicGeometry
