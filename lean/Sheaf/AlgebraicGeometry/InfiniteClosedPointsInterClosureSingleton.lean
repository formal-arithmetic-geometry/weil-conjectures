/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace

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

Proof: The scheme `X` is Jacobson by Tag 0478. If the closed points in `closure {z}`
were finite, their union of closed singletons would be closed. The Jacobson property says
that the closure of this union is `closure {z}`, so the union itself equals `closure {z}`.
In particular, `z` belongs to the union and is closed, contradicting the hypothesis. -/
theorem infinite_closedPoints_inter_closure_singleton
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (z : X) (hz : ¬ IsClosed ({z} : Set X)) :
    (closure ({z} : Set X) ∩ closedPoints X).Infinite := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  intro hfinite
  have hclosed : IsClosed (closure ({z} : Set X) ∩ closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closure ({z} : Set X) ∩ closedPoints X)]
    exact hfinite.isClosed_biUnion fun y hy ↦ hy.2
  have heq := closure_inter_closedPoints (X := X) (Z := closure ({z} : Set X))
    isClosed_closure
  rw [hclosed.closure_eq] at heq
  exact hz ((heq.symm ▸ (subset_closure (Set.mem_singleton z))).2)

end AlgebraicGeometry
