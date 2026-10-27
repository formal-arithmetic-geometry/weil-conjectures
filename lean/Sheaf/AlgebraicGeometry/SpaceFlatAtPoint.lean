/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Flatness at a point of an algebraic space

Source: Stacks Project, Morphisms of Spaces, definition-flat and Tag 04NG
(blueprint: def-sfb-space-flat-at-point).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.AlgebraicSpace

/-- Flatness at a point is witnessed on compatible étale scheme charts by flatness of
one scheme stalk map. The point is the existing field-valued point class, so no lift of
any particular geometric representative is required in the definition.
Source: Stacks Project, Morphisms of Spaces, definition-flat and Tag 04NG
(blueprint: def-sfb-space-flat-at-point). -/
def MapIsFlatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Point X.obj.obj) : Prop :=
  ∃ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj) (b : yoneda.obj V ⟶ Y.obj.obj)
    (h : U ⟶ V) (u : U.left),
    IsEtale a ∧ IsEtale b ∧ a ≫ f.hom.hom = yoneda.map h ≫ b ∧
      schemePointMap a u = x ∧ (h.left.stalkMap u).hom.Flat

end AlgebraicGeometry.AlgebraicSpace
