/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent

/-!
# Profinite connected-component quotient of a spectral space

The quotient of a spectral space by its connected components is compact Hausdorff and totally
disconnected.

## References

* [Stacks, Tag 0906]
-/

@[expose] public section

universe u

open Topology

/-- The connected-component quotient of a spectral space is compact Hausdorff and totally
disconnected, hence profinite in the topological sense. -/
theorem spectralSpace_connectedComponents_profinite
    {T : Type u} [TopologicalSpace T] [SpectralSpace T] :
    CompactSpace (ConnectedComponents T) ∧
      T2Space (ConnectedComponents T) ∧
        TotallyDisconnectedSpace (ConnectedComponents T) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end
