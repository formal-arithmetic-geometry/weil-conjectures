/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!

# The derived base-change morphism on bounded below derived categories

This file constructs the derived base-change morphism on the bounded below derived
categories (`DerivedCategory.Plus`). Fix a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : CommSq g' f' f g`. On the bounded below derived categories of étale
sheaves the derived pullback along `g` is the functor
`(Etale.upperStar A g).mapDerivedCategoryPlus` induced levelwise by the exact `g^*`
(no resolutions are needed), the derived pushforward along `f` is
`(Etale.lowerStar A f).rightDerivedFunctorPlus` computed via injective resolutions, and
they are related by the derived adjunction
`Etale.derivedUpperStarLowerStarAdjunctionPlus` of
`WeilConjectures.SixFunctors.Derived.UpperLowerStar`. This file constructs the *derived
base-change morphism*

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` (in diagrammatic `⋙`-order)

on the bounded below derived categories, as the composite of three named
transformations: unit insertion, square transport along the pullback comparison
`θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*`, and counit contraction.

The functoriality of `Functor.mapDerivedCategoryPlus` in natural isomorphisms and
compositions and its compatibility with the single functors are provided by
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

## Main definitions

- `AlgebraicGeometry.Etale.pullbackSquareComparison`: the pullback comparison `θ_sq`
  of a commutative square on the bounded below derived categories.
- `AlgebraicGeometry.Etale.baseChangeUnitStep`, `Etale.baseChangeSquareStep`,
  `Etale.baseChangeCounitStep`: the three steps of the construction.
- `AlgebraicGeometry.Etale.baseChange`: the derived base-change morphism `BC_sq`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Abelian

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section PullbackComposition

/-- The composition isomorphism `L(h₁ ≫ h₂)^* ≅ Lh₂^* ⋙ Lh₁^*` of derived pullbacks on
the bounded below derived categories: since the pullbacks are exact, the derived
pullbacks are the levelwise functors `mapDerivedCategoryPlus`, and the isomorphism is
obtained from the underived composition isomorphism `Etale.upperStarComp`. -/
noncomputable def Etale.upperStarPlusComp {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    (Etale.upperStar A (h₁ ≫ h₂)).mapDerivedCategoryPlus ≅
      (Etale.upperStar A h₂).mapDerivedCategoryPlus ⋙
        (Etale.upperStar A h₁).mapDerivedCategoryPlus :=
  Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarComp A h₁ h₂) ≪≫
    Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar A h₂) (Etale.upperStar A h₁)

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of a commutative
square `g' ≫ f = f' ≫ g` of schemes on the bounded below derived categories, obtained
from the composition isomorphisms of `Etale.upperStarPlusComp` and the commutativity of
the square. This comparison is the only square-specific categorical ingredient in the
construction of the base-change morphism. -/
noncomputable def Etale.pullbackSquareComparison (sq : CommSq g' f' f g) :
    (Etale.upperStar A g).mapDerivedCategoryPlus ⋙
        (Etale.upperStar A f').mapDerivedCategoryPlus ≅
      (Etale.upperStar A f).mapDerivedCategoryPlus ⋙
        (Etale.upperStar A g').mapDerivedCategoryPlus :=
  (Etale.upperStarPlusComp A f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫ Etale.upperStarPlusComp A g' f

/-- The *square transport* step `s_sq` of the base-change morphism on the bounded
below derived categories: the natural transformation obtained by transporting along the
pullback comparison `θ_sq` of the square under `Rf_*` on the left and `Rf'_*` on the
right; the reassociations are the only other ingredient. -/
noncomputable def Etale.baseChangeSquareStep (sq : CommSq g' f' f g) :
    ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus) ⋙
        ((Etale.upperStar A f').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) ≅
    ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
      (Etale.upperStar A f).mapDerivedCategoryPlus) ⋙
        ((Etale.upperStar A g').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (Etale.lowerStar A f).rightDerivedFunctorPlus
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      (Etale.pullbackSquareComparison A sq) (Etale.lowerStar A f').rightDerivedFunctorPlus ≪≫
        Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm

/-
lemma Etale.baseChangeSquareStep_app (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ((Etale.baseChangeSquareStep A sq).app K) =
      (lowerStar A f').rightDerivedFunctorPlus.mapIso
        ((pullbackSquareComparison A sq).app ((lowerStar A f).rightDerivedFunctorPlus.obj K)) := by
  apply Iso.ext
  simp only [baseChangeSquareStep, Functor.isoWhiskerLeft_trans, Iso.trans_assoc, NatIso.trans_app,
    Iso.trans_hom, Iso.app_hom, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.comp_id, Category.id_comp, Functor.mapIso_hom]
  exact (Category.id_comp _).trans (Category.comp_id _)
-/

end PullbackComposition

section BaseChangeTransformation

/- The K-flat resolution package on the coefficient category `A`, as in the sections
`DerivedUpperStar` and `DerivedUpperLowerStarAdjunction` of
`WeilConjectures.SixFunctors.Derived.UpperLowerStar`; it enters here through the bounded
below derived adjunction `Etale.derivedUpperStarLowerStarAdjunctionPlus`, which is
obtained by restriction of the unbounded derived adjunction. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A] [MonoidalClosed A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The *unit insertion* step `u_sq` of the base-change morphism on the bounded below
derived categories: the natural transformation
`Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the unit of the
derived adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def Etale.baseChangeUnitStep :
    (Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus ⟶
    ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus) ⋙
        ((Etale.upperStar A f').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
  ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙ (Etale.upperStar A g).mapDerivedCategoryPlus)
  (Etale.derivedUpperStarLowerStarAdjunctionPlus A f').unit

lemma Etale.baseChangeUnitStep_app (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChangeUnitStep A f g f').app K =
      (derivedUpperStarLowerStarAdjunctionPlus A f').unit.app
        (((lowerStar A f).rightDerivedFunctorPlus ⋙
          (upperStar A g).mapDerivedCategoryPlus).obj K) := by
  simp only [baseChangeUnitStep, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Category.id_comp]

/-- The *counit contraction* step `c_sq` of the base-change morphism on the bounded
below derived categories: the natural transformation obtained by contracting the
counit of the derived adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def Etale.baseChangeCounitStep :
    ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
      (Etale.upperStar A f).mapDerivedCategoryPlus) ⋙
        ((Etale.upperStar A g').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) ⟶
    (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
      (Etale.lowerStar A f').rightDerivedFunctorPlus :=
  Functor.whiskerRight
  (Etale.derivedUpperStarLowerStarAdjunctionPlus A f).counit
  ((Etale.upperStar A g').mapDerivedCategoryPlus ⋙ (Etale.lowerStar A f').rightDerivedFunctorPlus)
  ≫ (Functor.leftUnitor _).hom

lemma Etale.baseChangeCounitStep_app (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChangeCounitStep A f f' g').app K =
      (lowerStar A f').rightDerivedFunctorPlus.map
        ((upperStar A g').mapDerivedCategoryPlus.map
          ((derivedUpperStarLowerStarAdjunctionPlus A f).counit.app K)) := by
  simp only [baseChangeCounitStep, NatTrans.comp_app, Functor.whiskerRight_app, Functor.id_obj,
    Functor.comp_map, Functor.leftUnitor_hom_app]
  exact Category.comp_id _

variable {f g f' g'} in
/-- The *derived base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a
commutative square `g' ≫ f = f' ≫ g` of schemes on the bounded below derived
categories, assembled as the composite of the unit insertion, the square transport, and
the counit contraction.

Proper base change and smooth base change assert that this single morphism is an
isomorphism under two different sets of geometric hypotheses; no such hypothesis is
built into the definition. -/
noncomputable def Etale.baseChange (sq : CommSq g' f' f g) :
    (Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
      (Etale.upperStar A g).mapDerivedCategoryPlus ⟶
        (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus :=
  (Etale.baseChangeUnitStep A f g f') ≫ (Etale.baseChangeSquareStep A sq).hom ≫
    (Etale.baseChangeCounitStep A f f' g')

end BaseChangeTransformation

end AlgebraicGeometry
