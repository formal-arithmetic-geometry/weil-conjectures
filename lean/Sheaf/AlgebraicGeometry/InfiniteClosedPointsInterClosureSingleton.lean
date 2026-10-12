/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
import Sheaf.AlgebraicGeometry.InfiniteClosedPointsInterOfTopologicalKrullDimPos

/-!
# Infinitely many closed specializations of a nonclosed point

Source: Stacks Project, Tags 0478 and 0A21
(blueprint: lem-sc-finite-type-nonclosed-closure-closed-points).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nonclosed point of a scheme locally of finite type over an algebraically closed field
has infinitely many closed specializations. Source: Stacks Project, Tags 0478 and 0A21
(blueprint: lem-sc-finite-type-nonclosed-closure-closed-points).

Proof: Put `Z = closure {z}`. This is an irreducible closed subset with generic point `z`.
Since `z` is not closed, there is `y ≠ z` in `Z`. The irreducible closed subset `closure {y}`
is contained in `Z` and is strictly smaller: equality would give two distinct generic points
of the same irreducible closed subset of a scheme. This chain has length one, so `Z` has
positive dimension (Tag 0A21). Apply
`lem-sc-positive-dimensional-locally-algebraic-closed-points` to the irreducible closed subset
`Z` of the locally finite type scheme `X`. It gives infinitely many closed points of `X`
in `Z`, using the Jacobson property from Tag 0478. -/
theorem infinite_closedPoints_inter_closure_singleton
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (z : X) (hz : ¬ IsClosed ({z} : Set X)) :
    (closure ({z} : Set X) ∩ closedPoints X).Infinite := by
  sorry

end AlgebraicGeometry
