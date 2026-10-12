/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Finite.Stalk

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

Proof: Check the counit on geometric stalks of Spec k(D). A geometric point of that
spectrum has a separably closed extension field Ω and maps to the generic point of D.
The strict henselization of the local ring of D at this point is a separable closure
of k(D), since that local ring is k(D). Its base change along Spec k(D) -> D is itself.
The degree-zero strict-henselization stalk comparison therefore identifies the stalk
of eta_* F there with the geometric stalk of F. Pullback preserves geometric stalks,
and the comparison is the restriction map defining the counit, by the germ formula
for that counit. Thus the counit induces an isomorphism on each geometric stalk.
Geometric points are conservative for abelian etale sheaves, so the counit is an
isomorphism. This uses no assumption on the characteristic, torsion, or size of F. -/
theorem isIso_generic_direct_image_counit
    (D : Scheme.{u}) [IsIntegral D]
    (F : Sheaf (Spec D.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      D.fromSpecFunctionField).counit.app F) := by sorry

end AlgebraicGeometry.Etale
