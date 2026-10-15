/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.DerivedSectionPullbackPresentationComparison

/-! # The derived-unit leg of a presentation square

Source: Stacks Project, Tags 03Q8 and 0GIT.
The free-sheaf adjunction gives the first map in the restricted derived
section pullback; this file records the characterization used by the chart
assembly. -/

@[expose] public section
universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

theorem cartesianPresentation_derivedUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RawRestrictedComparison.derivedSectionPullback f =
      Functor.whiskerRight
          (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit
          (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y) ≫
        Functor.whiskerLeft D(upperStar AddCommGrpCat.{u + 1} f)
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{u + 1} f).hom := by
  exact derivedSectionPullback_eq_canonical f

end AlgebraicGeometry.Etale
