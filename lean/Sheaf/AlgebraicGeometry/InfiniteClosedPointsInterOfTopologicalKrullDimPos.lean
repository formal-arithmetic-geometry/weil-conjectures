/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.KrullDimension

/-!
# Infinitely many closed points in a positive-dimensional irreducible closed subset

Source: Stacks Project, Varieties, Tags 0478 and 0A21, with the affine positive-dimension
argument in Algebra (blueprint: lem-sc-positive-dimensional-locally-algebraic-closed-points).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- The original signature retains irreducibility, though the proof works without it.
set_option linter.unusedVariables false in
/-- An irreducible closed subset of positive topological Krull dimension in a scheme locally
of finite type over a field contains infinitely many ambient closed points. Source: Stacks
Project, Varieties, Tags 0478 and 0A21, and the affine positive-dimension argument in Algebra
(blueprint: lem-sc-positive-dimensional-locally-algebraic-closed-points).

Proof: The scheme `X` is Jacobson by Mathlib's locally finite type theorem (Tag 0478),
and the closed subspace `Z` is therefore Jacobson. The closed embedding of `Z` identifies
its closed points with the ambient closed points lying in `Z`. If there were only finitely
many of these, `JacobsonSpace.discreteTopology` would make `Z` discrete. Its topological
Krull dimension would then be at most zero, contradicting the positive dimension. -/
theorem infinite_closedPoints_inter_of_topologicalKrullDim_pos
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (Z : Set X) (hZclosed : IsClosed Z) (hZirred : IsIrreducible Z)
    (hZdim : 0 < topologicalKrullDim Z) :
    (Z ∩ closedPoints X).Infinite := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  have hι := hZclosed.isClosedEmbedding_subtypeVal
  have : JacobsonSpace Z := JacobsonSpace.of_isClosedEmbedding hι
  by_contra hfinite
  have hfinite : (Z ∩ closedPoints X).Finite := Set.not_infinite.mp hfinite
  have hpre : (Subtype.val ⁻¹' (Z ∩ closedPoints X) : Set Z).Finite :=
    hfinite.preimage Subtype.val_injective.injOn
  have heq : (Subtype.val ⁻¹' (Z ∩ closedPoints X) : Set Z) = closedPoints Z := by
    rw [Set.preimage_inter, hι.preimage_closedPoints]
    ext x
    simp
  have : DiscreteTopology Z := JacobsonSpace.discreteTopology (heq ▸ hpre)
  exact (not_lt_of_ge (topologicalKrullDim_zero_of_discreteTopology Z)) hZdim

end AlgebraicGeometry
