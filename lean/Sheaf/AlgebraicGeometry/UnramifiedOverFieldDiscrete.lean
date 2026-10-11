/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Limits

/-!
# Discreteness of a scheme unramified over a field

Source: Stacks Project, Morphisms, Lemma 02G7 (lemma-unramified-over-field),
part (1), topological part of the only-if direction
(blueprint: lem-weil-pbc-unramified-over-field-discrete).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme unramified over a field has discrete underlying topological space.
Source: Stacks Project, Morphisms, Lemma 02G7 (lemma-unramified-over-field), part (1)
(blueprint: lem-weil-pbc-unramified-over-field-discrete).

Proof: The unramified morphism is locally of finite type and quasi-finite at every point
by `lem-weil-pbc-unramified-quasi-finite-at-points` (Stacks 02V5), using
`def-weil-unramified-morphism` and `pqf-def-quasifinite`. The spectrum of the field has one
point (`def-weil-affine-spectrum`), so its fibre is the whole scheme. By
`lem-weil-pbc-quasi-finite-at-point-isolated` (Stacks 01TH), each point is open in that
fibre; local finite type is `def-weil-finite-type-morphism`. Every subset is the union
of its singletons, hence open, giving the discrete topology. Complements of singletons
are open as well, so points are also closed. -/
theorem discreteTopology_of_unramified_over_field {k : Type u} [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType g] [IsOpenImmersion (pullback.diagonal g)] :
    DiscreteTopology Y := by
  sorry

end AlgebraicGeometry
