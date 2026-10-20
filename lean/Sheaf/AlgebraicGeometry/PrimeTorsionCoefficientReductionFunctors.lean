/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionFoundation

/-!
# Punctual tensor source and target functors

Source: Stacks Project, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-functors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
/-- The source of the punctual tensor comparison, as a functor of the second sheaf.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-functors). -/
@[implicit_reducible]
def primeTensorSource (Λ : Type (u + 1)) [CommRing Λ]
    {X X' S' T : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S')
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ DerivedCategoryModule Λ X' :=
  primeSingle Λ T ⋙ primePushforward Λ g ⋙
    primePullback Λ f' ⋙
      (derivedTensor (ModuleCat.{u + 1} Λ) X').obj
        ((primePullback Λ p).obj
          ((primeSingle Λ X).obj E))

/-- The target of the punctual tensor comparison, as a functor of the second sheaf.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-functors). -/
@[implicit_reducible]
def primeTensorTarget (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y T : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ DerivedCategoryModule Λ X' :=
  primeSingle Λ T ⋙ primePullback Λ e ⋙
    (derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
      ((primePullback Λ h).obj
        ((primePullback Λ p).obj
          ((primeSingle Λ X).obj E))) ⋙
    primePushforward Λ h

/-- Functoriality in the first sheaf of the source expression.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-functors). -/
def primeTensorSourceMap (Λ : Type (u + 1)) [CommRing Λ]
    {X X' S' T : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S')
    {E E' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (δ : E ⟶ E') :
    primeTensorSource Λ p f' g E ⟶ primeTensorSource Λ p f' g E' :=
  Functor.whiskerLeft
    (primeSingle Λ T ⋙ primePushforward Λ g ⋙
      primePullback Λ f')
    ((derivedTensor (ModuleCat.{u + 1} Λ) X').map
      ((primePullback Λ p).map
        ((primeSingle Λ X).map δ)))

/-- Functoriality in the first sheaf of the target expression.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-functors). -/
def primeTensorTargetMap (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y T : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T)
    {E E' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (δ : E ⟶ E') :
    primeTensorTarget Λ p h e E ⟶ primeTensorTarget Λ p h e E' :=
  Functor.whiskerRight
    (Functor.whiskerLeft
      (primeSingle Λ T ⋙ primePullback Λ e)
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).map
        ((primePullback Λ h).map
          ((primePullback Λ p).map
            ((primeSingle Λ X).map δ)))))
    (primePushforward Λ h)

end AlgebraicGeometry.Etale


