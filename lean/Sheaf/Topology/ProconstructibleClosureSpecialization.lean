/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Constructible
import Sheaf.Topology.SpectralConstructibleFiniteIntersection

/-!
# Specializations in the closure of an intersection of constructible sets

Source: Stacks Project, Topology, Tag 0903, part (1)
(blueprint: lem-weil-pbc-spectral-proconstructible-closure-specialization).
-/

@[expose] public section

universe u v

namespace Topology

/-- In a spectral space, every point in the closure of an intersection of constructible sets
is a specialization of a point of that intersection. Source: Stacks Project, Topology,
Tag 0903, part (1)
(blueprint: lem-weil-pbc-spectral-proconstructible-closure-specialization).

Proof: Consider all quasi-compact open neighbourhoods of `x`. They are constructible by
`lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact` and
`def-weil-constructible-subset`. Finite intersections of these neighbourhoods are again
quasi-compact open neighbourhoods, by `def-weil-spectral-space`, including the empty
intersection, which is the quasi-compact space `X`. Each meets the intersection of the `E a`
since `x` belongs to its closure. Consequently the combined family of the `E a` and these
neighbourhoods has the finite intersection property.
By `lem-weil-pbc-spectral-constructible-finite-intersection`, choose `e` in all these sets.
Then `e` lies in every quasi-compact open neighbourhood of `x`. These form a neighbourhood
basis by `def-weil-spectral-space`, so every open neighbourhood of `x` contains `e`.
Thus `x` lies in the closure of the singleton `{e}`, as required. -/
theorem exists_mem_iInter_closure_singleton {X : Type u} [TopologicalSpace X]
    [SpectralSpace X] {A : Type v} (E : A → Set X)
    (hE : ∀ a : A, IsConstructible (E a)) {x : X} (hx : x ∈ closure (⋂ a : A, E a)) :
    ∃ e : X, e ∈ (⋂ a : A, E a) ∧ x ∈ closure ({e} : Set X) := by
  sorry

end Topology
