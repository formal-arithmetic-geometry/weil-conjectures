/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Connected.Clopen

import WeilConjectures.AlgebraicGeometry.GenericFibreClosedCoverSpread
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance
import WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty

/-!
# A lower bound for connected components near the generic fibre

Source: Stacks Project, More on Morphisms, Tag 055D,
`lemma-connected-components-in-neighbourhood`
(blueprint: lem-sfb-generic-connected-component-lower-bound).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a finite type morphism over a nonempty irreducible base, if the ordinary
residue-field fibre at the generic point has exactly `n` connected components,
all ordinary fibres on some open neighbourhood of that point have at least `n`.
An equivalence with `Fin n` expresses the exact generic count; an embedding of
`Fin n` expresses the lower bound, including `n = 0` and the empty generic fibre.

Source: Stacks Project, More on Morphisms, Tag 055D,
`lemma-connected-components-in-neighbourhood`
(blueprint: lem-sfb-generic-connected-component-lower-bound).

Proof:
1. If n = 0, take the whole base. Otherwise, use `Scheme.Hom.fiberHomeo` from
   `def-pc-scheme-fibre` to view the generic fibre as F = f⁻¹({η}) inside X.
   Enumerate its components A_i. By `lem-sfb-connected-component-maximality`,
   they cover F and are disjoint: meeting connected subsets have connected union.
   Each A_i is closed in F, since its closure in F is connected and maximality
   identifies this closure with A_i. Let C_i be its closure in X. Then
   C_i ∩ F = A_i, the C_i cover F, and their pairwise intersections miss F.
2. Apply `lem-sbc-generic-fibre-closed-cover-spread` to the finite closed union
   of the C_i and the empty set. Since closure {η} is the whole base, shrink
   to a neighbourhood where this union covers every fibre. Apply
   `lem-sbc-generic-fibre-closed-avoidance` to each pairwise intersection and
   intersect these finitely many neighbourhoods. On each resulting fibre the
   traces of the C_i are a pairwise disjoint finite closed cover.
3. Each C_i meets the generic fibre. Apply
   `lem-sbc-generic-closed-subset-fibre-nonempty` to each C_i and intersect the
   finitely many resulting opens. Every trace is now nonempty on every fibre
   over this open neighbourhood of η. This uses generic flatness and openness
   as packaged in that lemma, with no extra hypothesis on the base or morphism.
4. Every trace is also open, since its complement is the finite union of the
   other closed traces. Choose a point in each trace and its connected component,
   using `lem-sfb-connected-component-maximality`. Connectedness forces that
   component to stay in its clopen trace, so these n components are distinct.
   Transport them to the scheme fibre by `Scheme.Hom.fiberHomeo`. This gives
   the required embedding without extending any residue field.
-/
theorem exists_open_connectedComponents_fiber_lower_bound
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    [IrreducibleSpace S] (η : S) (hη : IsGenericPoint η Set.univ) (n : ℕ)
    (hn : Nonempty (ConnectedComponents (f.fiber η) ≃ Fin n)) :
    ∃ W : Set S, IsOpen W ∧ η ∈ W ∧
      ∀ s ∈ W, Nonempty (Fin n ↪ ConnectedComponents (f.fiber s)) := by
  sorry

end AlgebraicGeometry
