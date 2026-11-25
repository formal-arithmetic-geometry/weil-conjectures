/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Discrete representations of a topological group

The category of discrete representations of a topological group `G` over a ring `A`, i.e. those
in which every vector has an open stabilizer.
-/

@[expose] public section

universe u₁ v₁ w₁

namespace Rep

/-- The full subcategory of `Rep A G` on the representations in which the stabilizer of every
vector is open in `G`. -/
abbrev DiscreteContinuousRep (A : Type u₁) [Ring A] (G : Type v₁) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Type _ :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (fun X : Rep.{w₁} A G => ∀ x : X.V, IsOpen {g : G | X.ρ g x = x})

end Rep
