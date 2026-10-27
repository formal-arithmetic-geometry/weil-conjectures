/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Cartesian products of sheaves over an algebraic space

Source: Stacks Project, spaces-groupoids.tex, definition-group-space and Tag 04TW;
Mathlib.CategoryTheory.Monoidal.Cartesian.Over, `Over.cartesianMonoidalCategory`
(blueprint: def-sfb-group-space-over-cartesian).

The category of fppf sheaves over the base sheaf has its cartesian structure given by
sheaf fibre products. This registers Mathlib's explicit construction as the shared
instance used for internal group objects and actions over an algebraic-space base.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The pullback cartesian structure on fppf sheaves over an algebraic space.
Its unit is the identity of the base sheaf, and its binary products are sheaf pullbacks.
Source: Stacks, spaces-groupoids.tex, definition-group-space and Tag 04TW;
Mathlib's `Over.cartesianMonoidalCategory`
(blueprint: def-sfb-group-space-over-cartesian). -/
instance groupSpaceOverCartesian {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CartesianMonoidalCategory (Over B.obj) :=
  Over.cartesianMonoidalCategory B.obj

end AlgebraicGeometry.AlgebraicSpace
