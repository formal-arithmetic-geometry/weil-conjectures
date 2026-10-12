/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
import Sheaf.AlgebraicGeometry.InfiniteClosedPointsInterClosureSingleton

/-!
# Closed fibres under separation of closed points

Source: Stacks Project, Tag 0E8S, proof after condition (1), with Tag 0478
(blueprint: lem-sc-point-tangent-closed-fibre-singleton).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a scheme locally of finite type over an algebraically closed field, a morphism
injective on closed points has empty or singleton fibres over closed points, with the singleton
point closed in the source. Source: Stacks Project, Tag 0E8S, proof after condition (1),
with Tag 0478 (blueprint: lem-sc-point-tangent-closed-fibre-singleton).

Proof: Fix a closed point `p` of the target. Its inverse image is closed by continuity.
If a point of this inverse image were not closed in `X`,
`lem-sc-finite-type-nonclosed-closure-closed-points` would supply infinitely many closed points
in its closure. That closure lies in the inverse image, so all these points map to `p`,
contradicting injectivity on closed points. Thus every point in the fibre is closed.
If the fibre is nonempty, choose a point `x` in it. Every other point is closed by the same
argument, and injectivity on closed points forces it to equal `x`. Hence the fibre is empty
or exactly the singleton of a closed point. -/
theorem preimage_singleton_eq_empty_or_singleton_of_injOn_closedPoints
    (k : Type u) [Field k] [IsAlgClosed k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] (f : X ⟶ Y)
    (hf : Set.InjOn f (closedPoints X)) (p : Y) (hp : p ∈ closedPoints Y) :
    f ⁻¹' {p} = ∅ ∨ ∃ x : X, x ∈ closedPoints X ∧ f ⁻¹' {p} = {x} := by
  sorry

end AlgebraicGeometry
