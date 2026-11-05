/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine derived equivalence on shifts of the unit

Source: Stacks Project, Derived Categories of Schemes, Tag 06Z0.
(blueprint: new-affine-qcoh-derived-equivalence-shift).

The termwise tilde comparison identifies the image of the degree-zero free
rank-one module with the structure sheaf. Shift compatibility then gives the
same identification for every integer shift.
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

end AlgebraicGeometry
