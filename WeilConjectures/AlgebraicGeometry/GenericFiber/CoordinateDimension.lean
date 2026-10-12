/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension

/-!
# Coordinate projections lower the dimension of the generic fibre

Let `S` be an integral scheme, `f : X ⟶ S` locally of finite type and `t : X ⟶ 𝔸¹_S` a morphism
over `S` (a coordinate). The generic fibre of `t`, over the generic point of `𝔸¹_S`, has
dimension at most `dim X_K - 1`, where `X_K` is the generic fibre of `f`. This is the dimension
count driving the induction in Deligne's generic constructibility theorem
(`thm-fin-deligne-generic-open`).

Dimensions are topological Krull dimensions with values in `WithBot ℕ∞`, so an empty fibre has
dimension `⊥` and `⊥ + 1 = ⊥`.

## Main statements

- `AlgebraicGeometry.topologicalKrullDim_fiber_genericPoint_add_one_le`
  (`lem-fin-coordinate-generic-dimension`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `lem-fin-coordinate-generic-dimension`: Coordinate projections lower generic
dimension.

Let `S` be integral with function field `K`, let `f : X ⟶ S` be locally of finite type (in the
blueprint `X` is open in a closed subscheme of `𝔸ᵐ_S`) and let `t : X ⟶ 𝔸¹_S` be a morphism over
`S` (in the blueprint, a coordinate `t_r`). If `dim X_K ≤ n`, then the fibre of `t` over the
generic point of `𝔸¹_S` has dimension at most `n - 1`, an empty fibre having dimension `⊥`. -/
theorem topologicalKrullDim_fiber_genericPoint_add_one_le {S X : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFiniteType f] (t : X ⟶ 𝔸(PUnit; S))
    (ht : t ≫ 𝔸(PUnit; S) ↘ S = f) :
    topologicalKrullDim (t.fiber (genericPoint 𝔸(PUnit; S))) + 1 ≤
      topologicalKrullDim (f.fiber (genericPoint S)) :=
  sorry

end AlgebraicGeometry
