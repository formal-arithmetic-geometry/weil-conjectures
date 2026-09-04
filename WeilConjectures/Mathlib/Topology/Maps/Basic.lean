/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Constructions

/-!
# Closedness along a cover by open embeddings

`Topology.isClosed_of_isOpenEmbedding_cover`: a subset of a space covered by open
embeddings is closed as soon as its preimage in each member of the cover is closed.
-/

@[expose] public section

open Set

namespace Topology

/-- A set is closed as soon as its preimage under each member of a jointly surjective family
of open embeddings is closed. -/
lemma isClosed_of_isOpenEmbedding_cover {Q : Type*} [TopologicalSpace Q] {κ : Type*}
    {Z : κ → Type*} [∀ k, TopologicalSpace (Z k)] (q : ∀ k, Z k → Q)
    (hq : ∀ k, Topology.IsOpenEmbedding (q k)) (hcov : ∀ x : Q, ∃ k y, q k y = x)
    {s : Set Q} (hs : ∀ k, IsClosed (q k ⁻¹' s)) : IsClosed s := by
  rw [← isOpen_compl_iff]
  have hcompl : sᶜ = ⋃ k, q k '' ((q k ⁻¹' s)ᶜ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, y, rfl⟩ := hcov x
      exact Set.mem_iUnion.mpr ⟨k, y, hx, rfl⟩
    · intro hx
      obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact hy
  rw [hcompl]
  exact isOpen_iUnion fun k ↦ (hq k).isOpenMap _ (hs k).isOpen_compl

end Topology
