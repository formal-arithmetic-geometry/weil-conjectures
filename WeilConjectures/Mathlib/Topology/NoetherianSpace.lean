/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Separation.Connected

/-!
# Connected components of a noetherian space

A noetherian topological space has finitely many irreducible components, and every irreducible
component lies in a single connected component. Hence it has finitely many connected
components, and each of them is open, being the complement of the finitely many other ones.
-/

@[expose] public section

open Topology

variable {α : Type*} [TopologicalSpace α]

namespace TopologicalSpace.NoetherianSpace

variable [NoetherianSpace α]

/-- A noetherian space has finitely many connected components. -/
instance finite_connectedComponents : Finite (ConnectedComponents α) := by
  have : Finite (irreducibleComponents α) := finite_irreducibleComponents.to_subtype
  refine Finite.of_surjective (fun Z : irreducibleComponents α ↦
    (ConnectedComponents.mk (Z.2.1.nonempty.some) : ConnectedComponents α)) fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  refine ConnectedComponents.coe_eq_coe'.mpr ?_
  exact (irreducibleComponent_property x).1.isPreconnected.subset_connectedComponent
    mem_irreducibleComponent (isIrreducible_irreducibleComponent (x := x)).nonempty.some_mem

/-- Every connected component of a noetherian space is open. -/
theorem isOpen_connectedComponent (x : α) : IsOpen (connectedComponent x) :=
  ConnectedComponents.discreteTopology_iff.mp inferInstance x

end TopologicalSpace.NoetherianSpace
