/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Reduced algebraic spaces

Source: Stacks Project, Properties of Spaces, Tag 03E8 and definition-type-property,
with the reduced entry of remark-list-properties-local-etale-topology
(blueprint: def-sfb-reduced-algebraic-space).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is reduced when every scheme in its small etale site is reduced.
The scheme predicate is Mathlib's reducedness, equivalently reducedness of every local ring.
Source: Stacks Project, Properties of Spaces, Tag 03E8, definition-type-property and
remark-list-properties-local-etale-topology, reduced entry
(blueprint: def-sfb-reduced-algebraic-space). -/
def IsReduced {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ T : X.EtaleSite, AlgebraicGeometry.IsReduced ((etaleForget X).obj T)

end AlgebraicGeometry.AlgebraicSpace
