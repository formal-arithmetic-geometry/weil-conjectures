/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# ConstructibleTopology

Ported from the `proetale` package (`Proetale.Mathlib.Topology.Spectral.ConstructibleTopology`).
-/

@[expose] public section

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- A compact open is closed in the constructible topology. -/
lemma IsCompact.isClosed_constructibleTopology_of_isOpen {s : Set X}
    (hs : IsCompact s) (ho : IsOpen s) : IsClosed[constructibleTopology X] s := by
  rw [← @isOpen_compl_iff]
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  simp [constructibleTopologySubbasis, ho, hs]
