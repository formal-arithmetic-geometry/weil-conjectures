/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Surjectivity of maps that are both open and closed

The range of a map that is both open and closed is a clopen subset of the target, so it is
everything as soon as it is nonempty and the target is preconnected.

## Main results

- `IsOpenMap.surjective_of_isClosedMap`: a map from a nonempty space to a preconnected space
  that is both open and closed is surjective.
-/

@[expose] public section

/-- A map from a nonempty space to a preconnected space that is both open and closed is
surjective. -/
theorem IsOpenMap.surjective_of_isClosedMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [PreconnectedSpace Y] {f : X → Y} (ho : IsOpenMap f)
    (hc : IsClosedMap f) : Function.Surjective f :=
  Set.range_eq_univ.mp <|
    IsClopen.eq_univ ⟨hc.isClosed_range, ho.isOpen_range⟩ (Set.range_nonempty f)
