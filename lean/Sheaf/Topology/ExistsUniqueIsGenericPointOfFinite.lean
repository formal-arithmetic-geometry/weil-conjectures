/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Topology.Sober

/-!
# Finite T₀ spaces are sober

Source: Stacks Project, Topology, the finite-space claim in the proof of Tag 09XX,
with sobriety as in Definition Tag 004X (blueprint: lem-weil-pbc-finite-t0-space-sober).
-/

@[expose] public section

universe u

/-- Every irreducible closed subset of a finite T₀ space has a unique generic point.
Source: Stacks Project, Topology, proof of Tag 09XX and Definition Tag 004X
(blueprint: lem-weil-pbc-finite-t0-space-sober).

Proof (the elementary argument supplied by the DAG, since Stacks omits this argument):
1. An irreducible set contained in a nonempty finite union of closed sets lies in one
   member. Induct on the number of sets, using irreducibility for the first member and
   the union of the remaining members (def-weil-irreducible-components).
2. An irreducible closed set `Z` is nonempty and finite. Each point closure for a point
   of `Z` is contained in `Z`, and these finitely many closed sets cover `Z`. By step 1,
   one such closure contains all of `Z`, hence equals `Z`. Its point belongs to `Z`
   and is a generic point (def-weil-irreducible-components).
3. If two points have closure `Z`, an open set separating them by T₀ has a closed
   complement containing one point and therefore its closure `Z`. It cannot contain
   the other point, which belongs to `Z`, a contradiction. Thus the generic point
   is unique. -/
theorem existsUnique_isGenericPoint_of_finite (Y : Type u) [TopologicalSpace Y]
    [Finite Y] [T0Space Y] (Z : Set Y) (hZ : IsIrreducible Z) (hclosed : IsClosed Z) :
    ∃! η : Y, η ∈ Z ∧ IsGenericPoint η Z := by
  sorry
