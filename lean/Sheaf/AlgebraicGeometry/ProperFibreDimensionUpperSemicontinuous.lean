/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
import Sheaf.Topology.DimensionSupremumLocalDimensions
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Upper semicontinuity of proper fibre dimension

Source: Stacks Project, More on Morphisms, Tag 0D4I, lemma-dimension-fibres-proper
(blueprint: lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a proper morphism, the locus of fibres of dimension at most `d` is open.
The dimension of an empty fibre is bottom, so empty fibres belong to this locus.

Source: Stacks Project, More on Morphisms, Tag 0D4I, lemma-dimension-fibres-proper
(blueprint: lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous).

Proof:
1. Properness gives local finite type (`def-weil-proper-morphism`,
   `def-weil-finite-type-morphism`). By `lem-weil-pbc-local-fibre-dimension-open`,
   the locus in `X` where the local dimension in the fibre is at most `d` is open.
   Its complement `Z`, where the local fibre dimension is greater than `d`, is closed.
2. Properness implies universal closedness (`def-weil-proper-morphism`), hence the
   image `f(Z)` is closed by applying universal closedness to the identity base change.
3. The fibre projection identifies its points with the inverse image of `s`
   (`def-pc-scheme-fibre`). The dimension of a fibre is the supremum of its local
   dimensions (`lem-weil-pbc-dimension-supremum-local-dimensions`). Thus `s` lies
   in `f(Z)` exactly when its fibre has dimension greater than `d`. For an empty
   fibre, the supremum is bottom and there is no point of `Z` over `s`.
4. The desired locus is the complement of the closed set `f(Z)`, hence is open.
   No Noetherian or flatness assumption enters the argument.
-/
theorem isOpen_setOf_topologicalKrullDim_fiber_le
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (d : ℕ) :
    IsOpen {s : S | topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞)} := by
  sorry

end AlgebraicGeometry
