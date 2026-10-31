/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.CategoryTheory.SixFunctors.ParametrizedTensorHomSquare
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence

/-! # Geometric naturality of the ordinary coefficient Hom comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso
  AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison
  AlgebraicGeometry.Etale.ExceptionalCoefficients.tensorIso
  AlgebraicGeometry.Etale.scalarPullbackIso
  AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂
  AlgebraicGeometry.Etale.derivedTensorHomAdjunction
  AlgebraicGeometry.Etale.derivedHom
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private def uncurryTensorComparison
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
    (t : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) :
    Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj S where
  app Z := (t.app Z.1).app Z.2
  naturality X Y f := by
    have h := (Functor.uncurry.map t).naturality f
    change (F.map ((T.map f.1).app X.2) ≫
      F.map ((T.obj Y.1).map f.2)) ≫ (t.app Y.1).app Y.2 = _ at h
    change F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2) ≫ _ = _
    rw [F.map_comp]
    exact h

private def uncurryTensorIso
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
    (e : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) :
    Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj S :=
  NatIso.ofComponents (fun KL ↦ (e.app KL.1).app KL.2)
    (by
      intro X Y f
      exact (uncurryTensorComparison F T S e.hom).naturality f)

private def pullTensor (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) :
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) X) ⋙ Sites.pull A g ≅
      (Sites.pull A g).prod (Sites.pull A g) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) Y) :=
  uncurryTensorIso (Sites.pull A g)
    (derivedTensor (ModuleCat.{u + 1} A) X)
    (derivedTensor (ModuleCat.{u + 1} A) Y)
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) g)

set_option maxHeartbeats 2000000 in
-- The concrete derived comparison types require additional kernel reductions.
end WeilConjectures.FiniteFreeCoefficients
