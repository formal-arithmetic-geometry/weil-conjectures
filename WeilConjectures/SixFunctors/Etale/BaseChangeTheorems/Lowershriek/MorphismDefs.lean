/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!

# The base-change morphism for the lower shriek

Fix a Cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y`
of `f`. This file constructs the compact-support base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` (in diagrammatic `⋙`-order)

on the bounded below derived categories of étale sheaves, where `c' = c.baseChange sq`
is the base-changed compactification of `f'` and `Rf_!^c := i_! ⋙ Rp_*` is the derived
lower shriek associated with `c` — the bounded below derived incarnation of the lower
shriek `Compactification.lowerShriek` (`f_!^c = i_! ⋙ p_*`), in which the exact
extension by zero `i_!` needs no resolutions and only the pushforward is derived.

Following the construction of the reference (see `reference.tex` in this directory),
`Ex_!^c` is assembled from two exchange morphisms:

- the *direct-image exchange* `Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` for the proper
  square of the base-changed compactification, which is the base-change morphism
  `Etale.baseChange` of `WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs`
  (no properness enters its construction);
- the *extension-by-zero exchange* for the open-immersion square of the base-changed
  compactification. Its canonical mate goes in the direction
  `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*` (`Etale.openImmersionShriekBaseChange`); base change
  for extension by zero asserts that this mate is an isomorphism
  (`Etale.isIso_openImmersionShriekBaseChange`, currently `sorry`: on geometric stalks
  both sides are the pulled-back stalk on `X'` and vanish outside `X'`), and the
  construction of `Ex_!^c` uses its inverse, as in the reference.

The independence of `Ex_!^c` from the chosen compactification (Section 4 of the
reference) is *not* treated here; all statements are relative to an explicit
compactification `c`.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarSquareComparison`: the pullback comparison of a
  commutative square on the underived étale sheaf categories.
- `AlgebraicGeometry.Etale.openImmersionShriekBaseChange`: the canonical exchange
  morphism `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*` for a square of open immersions, with
  `Etale.isIso_openImmersionShriekBaseChange` (base change for extension by zero) and
  its bounded below derived form `Etale.openImmersionShriekBaseChangePlus`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlus`: the derived
  lower shriek `Rf_!^c = i_! ⋙ Rp_*` of a compactification on the bounded below derived
  categories.
- `AlgebraicGeometry.Etale.lowerShriekBaseChange`: the compact-support base-change
  morphism `Ex_!^c`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open Scheme Etale

/-! ### The extension-by-zero exchange morphism on underived sheaf categories -/

section OpenImmersion

variable {X Z X' Z' : Scheme.{u}}
  {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The *square transport* step `s_sq` of the extension-by-zero exchange morphism on the
bounded below derived categories: the natural isomorphism obtained by transporting along
the pullback comparison `θ_sq : Lj^* ∘ Lg'^* ≅ Lg^* ∘ Lj'^*` of the square
(`Etale.pullbackSquareComparison` applied to `sq.flip`) under `j_!` on the left and
`j'_!` on the right; the reassociations are the only other ingredient. -/
noncomputable def Etale.openImmersionLowerShriekBaseChangeSquareStep (sq : CommSq g' j' j g) :
    ((j)_!open[A].mapDerivedCategoryPlus ⋙ (j)^*[A].mapDerivedCategoryPlus) ⋙
        (g')^*[A].mapDerivedCategoryPlus ⋙ (j')_!open[A].mapDerivedCategoryPlus ≅
    ((j)_!open[A].mapDerivedCategoryPlus ⋙ (g)^*[A].mapDerivedCategoryPlus) ⋙
        (j')^*[A].mapDerivedCategoryPlus ⋙ (j')_!open[A].mapDerivedCategoryPlus :=
    Functor.squareTransport (j)_!open[A].mapDerivedCategoryPlus (j')_!open[A].mapDerivedCategoryPlus
      (Etale.pullbackSquareComparison A sq.flip)

lemma Etale.openImmersionLowerShriekBaseChangeSquareStep_app (sq : CommSq g' j' j g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.openImmersionLowerShriekBaseChangeSquareStep A sq).app K =
      (j')_!open[A].mapDerivedCategoryPlus.mapIso
        ((pullbackSquareComparison A sq.flip).app
          ((j)_!open[A].mapDerivedCategoryPlus.obj K)) := by
  simp [openImmersionLowerShriekBaseChangeSquareStep]

lemma Etale.openImmersionLowerShriekBaseChangeSquareStep_hom_app (sq : CommSq g' j' j g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.openImmersionLowerShriekBaseChangeSquareStep A sq).hom.app K =
      (j')_!open[A].mapDerivedCategoryPlus.map
        ((pullbackSquareComparison A sq.flip).hom.app
          ((j)_!open[A].mapDerivedCategoryPlus.obj K)) :=
  congrArg Iso.hom (Etale.openImmersionLowerShriekBaseChangeSquareStep_app A sq K)

lemma Etale.openImmersionLowerShriekBaseChangeSquareStep_inv_app (sq : CommSq g' j' j g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.openImmersionLowerShriekBaseChangeSquareStep A sq).inv.app K =
      (j')_!open[A].mapDerivedCategoryPlus.map
        ((pullbackSquareComparison A sq.flip).inv.app
          ((j)_!open[A].mapDerivedCategoryPlus.obj K)) :=
  congr(Iso.inv $(Etale.openImmersionLowerShriekBaseChangeSquareStep_app A sq K))

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Z X' Z' : Scheme.{u}}
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion j']

noncomputable def Etale.openImmersionLowerShriekBaseChangeUnitStep :
    (g')^*[A].mapDerivedCategoryPlus ⋙ (j')_!open[A].mapDerivedCategoryPlus ⟶
    ((j)_!open[A].mapDerivedCategoryPlus ⋙ (j)^*[A].mapDerivedCategoryPlus) ⋙
        (g')^*[A].mapDerivedCategoryPlus ⋙ (j')_!open[A].mapDerivedCategoryPlus :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
  (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j).unit
  ((g')^*[A].mapDerivedCategoryPlus ⋙ (j')_!open[A].mapDerivedCategoryPlus)

lemma Etale.openImmersionLowerShriekBaseChangeUnitStep_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.openImmersionLowerShriekBaseChangeUnitStep A j j' g').app K =
      (j')_!open[A].mapDerivedCategoryPlus.map
        ((g')^*[A].mapDerivedCategoryPlus.map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j).unit.app K)) := by
  simp [openImmersionLowerShriekBaseChangeUnitStep]

noncomputable def Etale.openImmersionLowerShriekBaseChangeCounitStep :
    ((j)_!open[A].mapDerivedCategoryPlus ⋙ (g)^*[A].mapDerivedCategoryPlus) ⋙
        (j')^*[A].mapDerivedCategoryPlus ⋙ (j')_!open[A].mapDerivedCategoryPlus ⟶
    (j)_!open[A].mapDerivedCategoryPlus ⋙ (g)^*[A].mapDerivedCategoryPlus :=
  Functor.whiskerLeft
  ((j)_!open[A].mapDerivedCategoryPlus ⋙ (g)^*[A].mapDerivedCategoryPlus)
  (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j').counit
    ≫ (Functor.rightUnitor _).hom

lemma Etale.openImmersionLowerShriekBaseChangeCounitStep_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.openImmersionLowerShriekBaseChangeCounitStep A j g j').app K =
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j').counit.app
        (((j)_!open[A].mapDerivedCategoryPlus ⋙ (g)^*[A].mapDerivedCategoryPlus).obj K) := by
  simp [openImmersionLowerShriekBaseChangeCounitStep]

variable {j g j' g'}

/-- The canonical exchange morphism `g'^* ⋙ j'_! ⟶ j_! ⋙ g^*` for a commutative square
```
X' --g'--> X
|          |
j'         j
v          v
Z' --g---> Z
```
of schemes with `j` and `j'` open immersions. -/
noncomputable def Etale.openImmersionLowerShriekBaseChange (sq : CommSq g' j' j g) :
    (g')^*[A].mapDerivedCategoryPlus ⋙ (j')_!open[A].mapDerivedCategoryPlus ⟶
      (j)_!open[A].mapDerivedCategoryPlus ⋙ (g)^*[A].mapDerivedCategoryPlus :=
  (Etale.openImmersionLowerShriekBaseChangeUnitStep A j j' g') ≫
    (Etale.openImmersionLowerShriekBaseChangeSquareStep A sq).hom ≫
      (Etale.openImmersionLowerShriekBaseChangeCounitStep A j g j')

/-- **Base change for extension by zero**: for a *Cartesian* square with `j` and `j'`
open immersions, the exchange morphism `ρ'^* ⋙ j'_! ⟶ j_! ⋙ ρ^*` is an isomorphism.

Mathematically, since the square is Cartesian, `X'` is the preimage of the open
subscheme `X ⊆ Z` under `ρ`, and on geometric stalks both sides are the pulled-back
stalk at points of `X'` and vanish outside `X'`. -/
theorem Etale.isIso_openImmersionShriekBaseChange (sq : IsPullback g' j' j g) :
    IsIso (Etale.openImmersionLowerShriekBaseChange A sq.toCommSq) :=
  sorry

noncomputable def Etale.openImmersionLowerShriekBaseChangeIso (sq : IsPullback g' j' j g) :
    (j)_!open[A].mapDerivedCategoryPlus ⋙ (g)^*[A].mapDerivedCategoryPlus ≅
      (g')^*[A].mapDerivedCategoryPlus ⋙ (j')_!open[A].mapDerivedCategoryPlus :=
  have := Etale.isIso_openImmersionShriekBaseChange A sq
  (asIso (Etale.openImmersionLowerShriekBaseChange A sq.toCommSq)).symm

end OpenImmersion

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

noncomputable def Etale.lowerShriekBaseChange (c : Compactification f)
    (sq : IsPullback g' f' f g) :
    Rf_!(c)[A]+ ⋙ (g)^*[A].mapDerivedCategoryPlus ⟶
    (g')^*[A].mapDerivedCategoryPlus ⋙ Rf_!(c.baseChange sq)[A]+ :=
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (c.i)_!open[A].mapDerivedCategoryPlus
  (Etale.baseChange A (c.baseChange_isPullback_g sq).toCommSq)
  ≫ (Functor.associator _ _ _).inv ≫
  (Functor.whiskerRight
  (Etale.openImmersionLowerShriekBaseChangeIso A (c.baseChange_isPullback_i sq)).hom
  R((c.baseChange sq).g)_*[A]+)
  ≫ (Functor.associator _ _ _).hom

end AlgebraicGeometry
