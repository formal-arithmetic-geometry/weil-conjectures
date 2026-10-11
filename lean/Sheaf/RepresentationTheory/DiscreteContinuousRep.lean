/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker M1
-/
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Topology.Algebra.Group.Defs

/-!
# Discrete modules with continuous group action

Source: Stacks Project, Etale Cohomology, Tag 04JP, and Injectives, Tag 04JF
(blueprint: def-exc-discrete-modules-category).
-/

universe u₁ v₁ w₁

namespace Rep

/-- (blueprint: def-exc-discrete-modules-category)
The category of left `A`-modules with an `A`-linear action of the topological group `G`
whose elements have open stabilizers, with equivariant linear maps. Stacks Project,
Etale Cohomology, Tag 04JP; Injectives, Tag 04JF. -/
abbrev DiscreteContinuousRep (A : Type u₁) [Ring A] (G : Type v₁) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Type _ :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (fun X : Rep.{w₁} A G => ∀ x : X.V, IsOpen {g : G | X.ρ g x = x})

end Rep
