/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.DerivedSectionPullbackPresentationComparison

/-! # The Leray/composition leg of a presentation square

Source: Stacks Project, Tags 03Q8, 0GIT, and 07A6. -/

@[expose] public section
universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

theorem cartesianPresentation_lerayComposition {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((RawRestrictedComparison.derivedSectionPullback f).app
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory.obj K)) ≫
      (cohomology AddCommGrpCat.{u + 1} X n).map
        ((Functor.mapDerivedCategoryNatIso
          (upperStarComp AddCommGrpCat.{u + 1} f g h hh) ≪≫
          Functor.mapDerivedCategoryCompIso
            (upperStar AddCommGrpCat.{u + 1} g)
            (upperStar AddCommGrpCat.{u + 1} f)).inv.app K) =
      presentationDerivedMap f g h hh K n := by
  exact derivedSectionPullback_presentation f g h hh K n

end AlgebraicGeometry.Etale
