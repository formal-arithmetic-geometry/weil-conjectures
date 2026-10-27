/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianStalk
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # Geometric set stalks of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 04JY (definition-stalk) and
04K0 (lemma-stalk-gives-point) (blueprint: def-sfb-space-geometric-set-stalk).

The neighbourhood category and its forgetful functor are the existing `PointedEtale`
and `pointedEtaleForget`. Set stalks use the section colimit in `Type (max (u + 1) w)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The set stalk is the colimit of the section diagram over `X.PointedEtale x` opposite.
On morphisms it is the induced colimit map. Its coefficient universe contains the
object universe of the neighbourhood category; no equality of universes is imposed.
For a geometric point take `G = Over.mk s` for `s : Spec Ω ⟶ S`, with Ω algebraically closed.
Source: Stacks 04JY, 04K0 (blueprint: def-sfb-space-geometric-set-stalk). -/
def etaleSetStalk {X : AlgebraicSpace S} {G : Over S}
    (x : yoneda.obj G ⟶ X.obj.obj) :
    Sheaf X.etaleTopology (Type (max (u + 1) w)) ⥤ Type (max (u + 1) w) :=
  sheafToPresheaf X.etaleTopology _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (X.pointedEtaleForget x).op ⋙ colim

/-- The canonical germ is the colimit cocone map at the specified pointed chart.
Source: Stacks 04JY, 04K0 (blueprint: def-sfb-space-geometric-set-stalk). -/
def etaleSetGerm {X : AlgebraicSpace S} {G : Over S}
    (x : yoneda.obj G ⟶ X.obj.obj)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (U : X.PointedEtale x) :
    F.obj.obj (op U.right) ⟶ (etaleSetStalk x).obj F :=
  colimit.ι ((X.pointedEtaleForget x).op ⋙ F.obj) (op U)

end AlgebraicGeometry.AlgebraicSpace
