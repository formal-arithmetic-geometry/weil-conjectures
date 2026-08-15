/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Derived
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!

# The derived base-change morphism on bounded below derived categories

This file is the bounded below (`DerivedCategory.Plus`) counterpart of
`WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism`. Fix a commutative
square of schemes

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
`WeilConjectures.SixFunctors.Derived`. This file constructs the *derived base-change
morphism*

`BC'_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` (in diagrammatic `⋙`-order)

on the bounded below derived categories, as the composite of the same three named
transformations as in the unbounded case: unit insertion, square transport along the
pullback comparison `θ'_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*`, and counit contraction.

The file also constructs the cohomological base-change morphism
`g^* H^q(Rf_* K) ⟶ H^q(Rf'_* Lg'^* K)` and its classical sheaf-level form
`g^* R^q f_* F ⟶ R^q f'_* g'^* F` for the higher direct images computed on the bounded
below derived categories.

The functoriality of `Functor.mapDerivedCategoryPlus` in natural isomorphisms and
compositions and its compatibility with the single functors are provided by
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and its
commutation with the homology functors by
`WeilConjectures.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`.

## Main definitions

- `AlgebraicGeometry.Etale.pullbackSquareComparison'`: the pullback comparison `θ'_sq`
  of a commutative square on the bounded below derived categories.
- `AlgebraicGeometry.Etale.baseChangeUnitStep'`, `Etale.baseChangeSquareStep'`,
  `Etale.baseChangeCounitStep'`: the three steps of the construction.
- `AlgebraicGeometry.Etale.baseChange'`: the derived base-change morphism `BC'_sq`.
- `AlgebraicGeometry.Etale.cohomologicalBaseChange'`: the cohomological base-change
  morphism.
- `AlgebraicGeometry.Etale.higherDirectImage'`: the higher direct image `R^n f_*`
  computed on the bounded below derived categories.
- `AlgebraicGeometry.Etale.sheafBaseChange'`: the classical base-change morphism
  `g^* R^n f_* F ⟶ R^n f'_* g'^* F` on sheaves.

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

/- Sheafification, pointwise left Kan extensions and chosen localized derived categories
for the small étale sites of all schemes at once, following the convention of
`WeilConjectures.ConstructibleSheaf.Defs`. -/
variable [∀ (T : Scheme.{u}), HasWeakSheafify T.smallEtaleTopology A]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T : Scheme.{u}), HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology A)]

/- The K-flat resolution package on the coefficient category `A`, as in the sections
`DerivedUpperStar` and `DerivedUpperLowerStarAdjunction` of
`WeilConjectures.SixFunctors.Derived`; it enters here through the bounded below derived
adjunction `Etale.derivedUpperStarLowerStarAdjunctionPlus`, which is obtained by
restriction of the unbounded derived adjunction. -/
variable [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]
  [HasColimitsOfShape (Discrete ℤ) A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A]

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

/-- The pullback comparison `θ'_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of a commutative
square `g' ≫ f = f' ≫ g` of schemes on the bounded below derived categories, obtained
from the composition isomorphisms of `Etale.upperStarPlusComp` and the commutativity of
the square. This comparison is the only square-specific categorical ingredient in the
construction of the base-change morphism. -/
noncomputable def Etale.pullbackSquareComparison' (sq : CommSq g' f' f g) :
    (Etale.upperStar A g).mapDerivedCategoryPlus ⋙
        (Etale.upperStar A f').mapDerivedCategoryPlus ≅
      (Etale.upperStar A f).mapDerivedCategoryPlus ⋙
        (Etale.upperStar A g').mapDerivedCategoryPlus :=
  (Etale.upperStarPlusComp A f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫ Etale.upperStarPlusComp A g' f

end PullbackComposition

section BaseChangeTransformation

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *unit insertion* step `u'_sq` of the base-change morphism on the bounded below
derived categories: the natural transformation
`Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the unit of the
derived adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def Etale.baseChangeUnitStep' :
    (Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
        (Etale.upperStar A g).mapDerivedCategoryPlus ⟶
      ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
          (Etale.upperStar A g).mapDerivedCategoryPlus) ⋙
        ((Etale.upperStar A f').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
        (Etale.upperStar A g).mapDerivedCategoryPlus)
      (Etale.derivedUpperStarLowerStarAdjunctionPlus A f').unit

/-- The *square transport* step `s'_sq` of the base-change morphism on the bounded
below derived categories: the natural transformation obtained by transporting along the
pullback comparison `θ'_sq` of the square under `Rf'_*`. -/
noncomputable def Etale.baseChangeSquareStep' (sq : CommSq g' f' f g) :
    ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
          (Etale.upperStar A g).mapDerivedCategoryPlus) ⋙
        ((Etale.upperStar A f').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) ⟶
      (Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
        (((Etale.upperStar A f).mapDerivedCategoryPlus ⋙
            (Etale.upperStar A g').mapDerivedCategoryPlus) ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((Etale.lowerStar A f).rightDerivedFunctorPlus)
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.pullbackSquareComparison' A sq).hom
          ((Etale.lowerStar A f').rightDerivedFunctorPlus))

/-- The *counit contraction* step `c'_sq` of the base-change morphism on the bounded
below derived categories: the natural transformation
`Rf'_* ∘ Lg'^* ∘ Lf^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` obtained by contracting with the counit
of the derived adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def Etale.baseChangeCounitStep' :
    (Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
        (((Etale.upperStar A f).mapDerivedCategoryPlus ⋙
            (Etale.upperStar A g').mapDerivedCategoryPlus) ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) ⟶
      (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
        (Etale.lowerStar A f').rightDerivedFunctorPlus :=
  Functor.whiskerLeft ((Etale.lowerStar A f).rightDerivedFunctorPlus)
      (Functor.associator _ _ _).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Etale.derivedUpperStarLowerStarAdjunctionPlus A f).counit
      ((Etale.upperStar A g').mapDerivedCategoryPlus ⋙
        (Etale.lowerStar A f').rightDerivedFunctorPlus) ≫
    (Functor.leftUnitor _).hom

/-- The *derived base-change morphism* `BC'_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a
commutative square `g' ≫ f = f' ≫ g` of schemes on the bounded below derived
categories, assembled as the composite of the unit insertion, the square transport, and
the counit contraction.

Proper base change and smooth base change assert that this single morphism is an
isomorphism under two different sets of geometric hypotheses (see
`WeilConjectures.SixFunctors.ProperBaseChange.Proper'` and
`WeilConjectures.SixFunctors.ProperBaseChange.Smooth'`); no such hypothesis is built
into the definition. -/
noncomputable def Etale.baseChange' (sq : CommSq g' f' f g) :
    (Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
        (Etale.upperStar A g).mapDerivedCategoryPlus ⟶
      (Etale.upperStar A g').mapDerivedCategoryPlus ⋙
        (Etale.lowerStar A f').rightDerivedFunctorPlus :=
  Etale.baseChangeUnitStep' A ≫ Etale.baseChangeSquareStep' A sq ≫
    Etale.baseChangeCounitStep' A

end BaseChangeTransformation

section CohomologicalBaseChange

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *cohomological base-change morphism* of a commutative square on the bounded
below derived categories: the natural transformation
`g^* H^n(Rf_* K) ⟶ H^n(Rf'_* Lg'^* K)`, obtained by composing the exactness comparison
for `g` with the `n`-th homology of the derived base-change morphism `BC'_sq`. -/
noncomputable def Etale.cohomologicalBaseChange' (sq : CommSq g' f' f g) (n : ℤ) :
    ((Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology A) n) ⋙
      Etale.upperStar A g ⟶
      ((Etale.upperStar A g').mapDerivedCategoryPlus ⋙
          (Etale.lowerStar A f').rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology A) n :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((Etale.lowerStar A f).rightDerivedFunctorPlus)
      (Functor.mapDerivedCategoryPlusHomologyFunctorIso (Etale.upperStar A g) n).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Etale.baseChange' A sq)
      (DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology A) n)

end CohomologicalBaseChange

section SheafBaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The higher direct image `R^n f_* : Sh(X_ét) ⥤ Sh(Y_ét)` computed on the bounded
below derived categories: the `n`-th homology sheaf of the derived pushforward of a
sheaf placed in degree `0`, `R^n f_* F := H^n(Rf_*(F[0]))`. -/
noncomputable def Etale.higherDirectImage' (n : ℤ) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙
    (Etale.lowerStar A f).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology A) n

variable {X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The classical *base-change morphism on sheaves*
`g^* R^n f_* F ⟶ R^n f'_* g'^* F` of a commutative square, obtained from the
cohomological base-change morphism on the bounded below derived categories evaluated on
sheaves placed in degree `0`. -/
noncomputable def Etale.sheafBaseChange' (sq : CommSq g' f' f g) (n : ℤ) :
    Etale.higherDirectImage' A f n ⋙ Etale.upperStar A g ⟶
      Etale.upperStar A g' ⋙ Etale.higherDirectImage' A f' n :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology A) 0)
      (Etale.cohomologicalBaseChange' A sq n) ≫
    Functor.whiskerLeft
      (DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology A) 0)
      (Functor.associator _ _ _).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapDerivedCategoryPlusSingleFunctor (Etale.upperStar A g') 0).hom
      ((Etale.lowerStar A f').rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology A) n) ≫
    (Functor.associator _ _ _).hom

end SheafBaseChange

end AlgebraicGeometry
