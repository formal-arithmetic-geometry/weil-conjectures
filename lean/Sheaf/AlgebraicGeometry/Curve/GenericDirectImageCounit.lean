/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.Curve.GenericPointedEtaleCofinality

/-! # The counit at the generic point of an integral scheme

Source: blueprint `lem-sc-affine-generic-second`, proof paragraph 3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Generic restriction of generic direct image recovers the original sheaf.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraph 3, generic counit.
(blueprint: lem-sc-generic-direct-image-counit)

Proof: Check the counit on geometric stalks of Spec k(D). Base change to the generic
point is initial on pointed étale neighbourhoods: neighbourhoods over the function
field extend after clearing denominators, and the open agreement locus of two
pointed maps lifts to an open before base change because the generic inclusion
is a preimmersion. Its opposite is final, so the colimit restriction map defining
`stalkRestrict` is an isomorphism. The germ formula `stalkRestrict_eq_counit` identifies
this restriction with the stalk of the counit after the inverse-image stalk
isomorphism. Cancel that isomorphism and transport along `uliftSheafFiberIso` to
the conservative family of universe-lifted geometric stalks. Conservativity gives
the asserted isomorphism. No characteristic or torsion assumption is used. -/
theorem isIso_generic_direct_image_counit
    (D : Scheme.{u}) [IsIntegral D]
    (F : Sheaf (Spec D.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField).counit.app F) := by
  apply Scheme.isIso_of_isIso_sheafFiber_map
  intro x
  let s := (Spec D.functionField).algClosurePoint x
  have hi := Scheme.initial_generic_baseChangeNbhd D s
  have hrestrict : IsIso (stalkRestrict AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField (s ≫ D.fromSpecFunctionField) ⟨s, rfl⟩ F) := by
    unfold stalkRestrict
    infer_instance
  have hstalk : IsIso ((Scheme.pointSmallEtale s).sheafFiber.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        D.fromSpecFunctionField).counit.app F)) := by
    have hcomp := stalkRestrict_eq_counit AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField s F
    have : IsIso ((upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
        D.fromSpecFunctionField s).inv.app
          ((lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj F) ≫
        (Scheme.pointSmallEtale s).sheafFiber.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
            D.fromSpecFunctionField).counit.app F)) := by
      rw [← hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
        D.fromSpecFunctionField s).inv.app
          ((lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj F)) _
  let c := (Scheme.pointSmallEtale s).uliftSheafFiberIso.{u + 1} AddCommGrpCat.{u + 1}
  have hn := c.hom.naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField).counit.app F)
  have : IsIso (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        D.fromSpecFunctionField).counit.app F) ≫ c.hom.app F) := by
    erw [hn]
    infer_instance
  change IsIso (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber.map _)
  exact IsIso.of_isIso_comp_right _ (c.hom.app F)

end AlgebraicGeometry.Etale
