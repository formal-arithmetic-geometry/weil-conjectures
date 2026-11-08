/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Intersection restriction becomes invertible on its open

Source: Stacks Project, Tag 02FU, restriction to a member of the covering.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
noncomputable section

/-- Restrict a module presheaf to intersections with W, retaining scalars on the test open.
Source: Stacks Project, Tag 02FU, restriction on intersection sections. -/
def cechCapPresheafFunctor {X : Scheme.{u}} (W : X.Opens) :
    PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      PresheafOfModules.{u} X.ringCatSheaf.obj :=
  PresheafOfModules.pushforward (cechCapRingMap W)

end
end AlgebraicGeometry
