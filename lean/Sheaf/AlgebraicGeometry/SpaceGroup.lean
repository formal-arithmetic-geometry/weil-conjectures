/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.Algebra.Group.Hom.Basic

/-! # General group laws on algebraic spaces

Source: Stacks Project, Groupoids in Algebraic Spaces, Tag 043H,
definition-group-space (blueprint: def-sfb-space-group).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A group algebraic space, specified by its natural group law on the functor of
points. Commutativity and smoothness are not imposed. Naturality of inverse follows
from the multiplication and identity equations for group homomorphisms.
Source: Stacks, Tag 043H, definition-group-space
(blueprint: def-sfb-space-group). -/
structure SpaceGroup {S : Scheme.{u}} (G : AlgebraicSpace S) where
  group (T : (Over S)ᵒᵖ) : Group (G.obj.obj.obj T)
  map_mul {T U : (Over S)ᵒᵖ} (f : T ⟶ U) (x y : G.obj.obj.obj T) :
    G.obj.obj.map f (@Mul.mul _ (group T).toMul x y) =
      @Mul.mul _ (group U).toMul (G.obj.obj.map f x) (G.obj.obj.map f y)
  map_one {T U : (Over S)ᵒᵖ} (f : T ⟶ U) :
    G.obj.obj.map f (@One.one _ (group T).toOne) = @One.one _ (group U).toOne

/-- Identity at a test scheme. Source: Stacks, Tag 043H, definition-group-space
(blueprint: def-sfb-space-group). -/
def SpaceGroup.onePoint {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : SpaceGroup G) (T : Over S) : G.obj.obj.obj (op T) :=
  @One.one _ (H.group (op T)).toOne

/-- Product of two test points, given by the actual group multiplication.
Source: Stacks, Tag 043H, definition-group-space (blueprint: def-sfb-space-group). -/
def SpaceGroup.mulPoint {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : SpaceGroup G) (T : Over S) (x y : G.obj.obj.obj (op T)) :
    G.obj.obj.obj (op T) :=
  @Mul.mul _ (H.group (op T)).toMul x y

end AlgebraicGeometry.AlgebraicSpace
