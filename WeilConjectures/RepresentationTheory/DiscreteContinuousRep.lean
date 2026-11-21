/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Discrete continuous representations

The full subcategory of `Rep A G` on representations whose vectors have open stabilizers.
-/

@[expose] public section

universe u₁ v₁ w₁

namespace Rep

/-- The category of discrete continuous representations of a topological group `G`: the
representations in which every vector has an open stabilizer. -/
abbrev DiscreteContinuousRep (A : Type u₁) [Ring A] (G : Type v₁) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Type _ :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (fun X : Rep.{w₁} A G => ∀ x : X.V, IsOpen {g : G | X.ρ g x = x})

end Rep
