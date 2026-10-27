/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q93 and NV
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianStalk

/-! # Set-valued pointed étale stalks on an algebraic space

Source: Stacks Project, Properties of Spaces, Tags 04JY and 04K0
(blueprint: def-sfb-space-pointed-set-stalk).

The neighbourhood category and chart projection are the existing `PointedEtale`
and `pointedEtaleForget`. The stalk is their actual section colimit in the containing
universe, with its induced functor on sheaf maps and its colimit-cocone germs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The set-valued stalk is the colimit over opposite pointed étale neighbourhoods.
Source: Stacks, Tag 04JY and Tag 04K0
(blueprint: def-sfb-space-pointed-set-stalk). -/
def pointedSetStalk (X : AlgebraicSpace S) {P : Over S}
    (x : yoneda.obj P ⟶ X.obj.obj) :
    Sheaf X.etaleTopology (Type (max (u + 1) w)) ⥤ Type (max (u + 1) w) :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (X.pointedEtaleForget x).op ⋙ colim

/-- The germ map is the colimit cocone at the specified pointed neighbourhood.
Source: Stacks, Tag 04JY
(blueprint: def-sfb-space-pointed-set-stalk). -/
def pointedSetGerm (X : AlgebraicSpace S) {P : Over S}
    (x : yoneda.obj P ⟶ X.obj.obj) (N : X.PointedEtale x)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w))) :
    F.obj.obj (op N.right) ⟶ (X.pointedSetStalk x).obj F :=
  colimit.ι ((X.pointedEtaleForget x).op ⋙ F.obj) (op N)

end AlgebraicGeometry.AlgebraicSpace
