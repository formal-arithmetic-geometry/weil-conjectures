/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackTransport
public import Sheaf.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison

/-! # Derived section pullback and the presentation map -/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The restricted-section pullback is the derived adjunction unit followed by Leray. -/
theorem derivedSectionPullback_eq_canonical {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RawRestrictedComparison.derivedSectionPullback f =
      Functor.whiskerRight
          (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit
          (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y) ≫
        Functor.whiskerLeft D(upperStar AddCommGrpCat.{u + 1} f)
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{u + 1} f).hom := by
  rfl

/-- Degree-`n` homology of the section pullback is the canonical presentation map. -/
theorem derivedSectionPullback_presentation {X Y T : Scheme.{u}}
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
  rw [derivedSectionPullback_eq_canonical]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp]
  rfl

end AlgebraicGeometry.Etale
