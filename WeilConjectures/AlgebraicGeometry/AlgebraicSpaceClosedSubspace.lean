/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Basic

/-! # Closed subspaces of an algebraic space

Source: Stacks Project, Morphisms of Spaces, Tag 03MB
(blueprint: def-sfb-space-closed-subspace).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Closed subspaces are subobjects whose scheme base changes are closed immersions.
Subobjects identify isomorphic presentations over the ambient space; their order is
inclusion of subfunctors, including the scheme structures.
Source: Stacks Project, Morphisms of Spaces, Tag 03MB
(blueprint: def-sfb-space-closed-subspace). -/
abbrev ClosedSubspace {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  {C : Subobject X //
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) C.arrow.hom.hom}

end AlgebraicGeometry.AlgebraicSpace
