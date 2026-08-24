/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Derived
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale
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
- `AlgebraicGeometry.Compactification.rightDerivedLowerShriekPlus`: the derived lower
  shriek `Rf_!^c = i_! ⋙ Rp_*` of a compactification on the bounded below derived
  categories.
- `AlgebraicGeometry.Etale.lowerShriekBaseChange`: the compact-support base-change
  morphism `Ex_!^c`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

/-! ### The extension-by-zero exchange morphism on underived sheaf categories -/

section OpenImmersion

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {X Z X' Z' : Scheme.{u}}
  {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The *square transport* step `s_sq` of the extension-by-zero exchange morphism on the
bounded below derived categories: the natural isomorphism obtained by transporting along
the pullback comparison `θ_sq : Lj^* ∘ Lg'^* ≅ Lg^* ∘ Lj'^*` of the square
(`Etale.pullbackSquareComparison` applied to `sq.flip`) under `j_!` on the left and
`j'_!` on the right; the reassociations are the only other ingredient. -/
noncomputable def Etale.openImmersionLowerShriekBaseChangeSquareStep (sq : CommSq g' j' j g) :
    ((Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
      (Etale.upperStar A j).mapDerivedCategoryPlus) ⋙
        (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
          (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus ≅
    ((Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus) ⋙
        (Etale.upperStar A j').mapDerivedCategoryPlus ⋙
          (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        (Etale.pullbackSquareComparison A sq.flip)
          (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus ≪≫
            Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm

lemma Etale.openImmersionLowerShriekBaseChangeSquareStep_app (sq : CommSq g' j' j g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ((Etale.openImmersionLowerShriekBaseChangeSquareStep A sq).app K) =
      (openImmersionLowerShriek A j').mapDerivedCategoryPlus.mapIso
        ((pullbackSquareComparison A sq.flip).app
          ((openImmersionLowerShriek A j).mapDerivedCategoryPlus.obj K)) := by
  apply Iso.ext
  simp only [openImmersionLowerShriekBaseChangeSquareStep, Functor.isoWhiskerLeft_trans,
    Iso.trans_assoc, NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.comp_id, Category.id_comp,
    Functor.mapIso_hom]
  exact (Category.id_comp _).trans (Category.comp_id _)

variable [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A] [MonoidalClosed A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Z X' Z' : Scheme.{u}}
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion j']

noncomputable def Etale.openImmersionLowerShriekBaseChangeUnitStep :
    (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
      (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus ⟶
    ((Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
      (Etale.upperStar A j).mapDerivedCategoryPlus) ⋙
        (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
          (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
  (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j).unit
  ((Etale.upperStar A g').mapDerivedCategoryPlus ⋙
    (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus)

lemma Etale.openImmersionLowerShriekBaseChangeUnitStep_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.openImmersionLowerShriekBaseChangeUnitStep A j j' g').app K =
      (openImmersionLowerShriek A j').mapDerivedCategoryPlus.map
        ((upperStar A g').mapDerivedCategoryPlus.map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j).unit.app K)) := by
  simp only [openImmersionLowerShriekBaseChangeUnitStep, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map, Category.id_comp]

noncomputable def Etale.openImmersionLowerShriekBaseChangeCounitStep :
    ((Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus) ⋙
        (Etale.upperStar A j').mapDerivedCategoryPlus ⋙
          (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus ⟶
    (Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus :=
  Functor.whiskerLeft
  ((Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
    (Etale.upperStar A g).mapDerivedCategoryPlus)
  (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j').counit
    ≫ (Functor.rightUnitor _).hom

lemma Etale.openImmersionLowerShriekBaseChangeCounitStep_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.openImmersionLowerShriekBaseChangeCounitStep A j g j').app K =
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j').counit.app
        (((openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
          (upperStar A g).mapDerivedCategoryPlus).obj K) := by
  simp only [openImmersionLowerShriekBaseChangeCounitStep, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact Category.comp_id _

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
    (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
      (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus ⟶
        (Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
          (Etale.upperStar A g).mapDerivedCategoryPlus :=
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
    (Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus ≅
        (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
          (Etale.openImmersionLowerShriek A j').mapDerivedCategoryPlus :=
  have := Etale.isIso_openImmersionShriekBaseChange A sq
  (asIso (Etale.openImmersionLowerShriekBaseChange A sq.toCommSq)).symm

end OpenImmersion

/-

section DerivedLowerShriek

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The derived lower shriek `Rf_!^c : D^+(X_ét) ⥤ D^+(Y_ét)` associated with a
compactification `c : X ⟶[i] Z ⟶[p] Y` of `f` on the bounded below derived categories
of étale sheaves: the extension by zero `i_!` applied levelwise (it is exact, so no
resolutions are needed), followed by the right derived pushforward `Rp_*`.

This is the bounded below derived incarnation of the lower shriek
`Compactification.lowerShriek` (`f_!^c = i_! ⋙ p_*`) associated with `c`, following
the definition `Rf_! K := Rp_* i_! K` of the reference; it depends on the chosen
compactification, the comparison between different choices being the independence-of-
compactification theorem, which is not treated here. -/
noncomputable def Compactification.rightDerivedLowerShriekPlus (c : Compactification f) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus ⋙
    (Etale.lowerStar A c.g).rightDerivedFunctorPlus

end DerivedLowerShriek

section LowerShriekBaseChange

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *compact-support base-change morphism*
`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` of a Cartesian square
`sq : IsPullback g' f' f g` for a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`, where
`c' = c.baseChange sq` is the base-changed compactification of `f'`, on the bounded
below derived categories of étale sheaves.

Following the reference, it is the composite of the direct-image exchange
`Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` (`Etale.baseChange`) for the proper square of
the base-changed compactification, whiskered with `i_!`, and the inverse of the
extension-by-zero exchange isomorphism `Lg'^* ⋙ i'_! ≅ i_! ⋙ Lḡ^*`
(`Etale.openImmersionShriekBaseChangePlus`) for its open-immersion square, whiskered
with `Rp'_*`.

Proper base change asserts that this morphism is an isomorphism (the direct-image
exchange is one by proper base change for the proper morphism `p`); no such assertion is
built into the definition. -/
noncomputable def Etale.lowerShriekBaseChange (c : Compactification f)
    (sq : IsPullback g' f' f g) :
    c.rightDerivedLowerShriekPlus A ⋙ (Etale.upperStar A g).mapDerivedCategoryPlus ⟶
      (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
        (c.baseChange sq).rightDerivedLowerShriekPlus A :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus
      (Etale.baseChange A (c.baseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Etale.openImmersionShriekBaseChangePlus A (c.baseChange_isPullback_i sq)).inv
      ((Etale.lowerStar A (c.baseChange sq).g).rightDerivedFunctorPlus) ≫
    (Functor.associator _ _ _).hom

end LowerShriekBaseChange
-/

end AlgebraicGeometry
