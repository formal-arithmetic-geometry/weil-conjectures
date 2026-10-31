/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.Topology.KrullDimension

/-! # Dimension of intersections in projective space

Source: Stacks Project, Tag 0B2R, `varieties-lemma-intersection-in-projective-space`
(blueprint: lem-sfb-projective-closed-intersection-dimension).

Nonempty closed subsets of projective space intersect when their dimensions add up to
at least the ambient dimension, with the expected lower bound on intersection dimension.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The projective intersection dimension theorem for arbitrary closed subsets over a field.

Source: Stacks Project, Tag 0B2R, `varieties-lemma-intersection-in-projective-space`
(blueprint: lem-sfb-projective-closed-intersection-dimension).

Proof:
1. By `def-kun-topological-krull-dimension`, a finite dimension is attained by a chain
   of irreducible closed subsets. Its largest member has the same dimension. Thus choose
   irreducible closed subsets of `X` and `Y` of dimensions `r` and `s`. A lower bound for
   their intersection transfers to `X ∩ Y` by inclusion of irreducible closed chains.
2. By `lem-sfb-projective-affine-cone-dimension`, their affine cones in affine `(N+1)`-space
   are irreducible closed subsets of dimensions `r+1` and `s+1`, both containing the origin.
   Irreducibility implies equidimensionality.
3. Apply `lem-sfb-affine-closed-intersection-dimension` to these cones: their intersection
   is nonempty because it contains the origin, and its dimension is at least
   `(r+1)+(s+1)-(N+1) = r+s-N+1`, which is at least one by the numerical hypothesis.
4. The intersection of the cones is the cone of the projective intersection, by the
   defining inverse-image formula. An empty projective intersection would have singleton
   cone, of dimension zero, contradicting step 3. The nonempty projective intersection
   has finite dimension bounded by `r`, by inclusion of closed chains. Apply the cone
   dimension formula again and subtract one to obtain the bound. Transfer both conclusions
   from the chosen irreducible subsets to `X` and `Y` as in step 1.

The coordinate index is the universe lift of `Fin (N+1)`. The parameters `r` and `s`
are nonnegative integers encoded as naturals; under `hSum` natural subtraction agrees
with the nonnegative integer difference in the source. -/
theorem ProjectiveSpace.closed_intersection_dimension (k : Type u) [Field k] (N : ℕ)
    (X Y : Set (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k))))
    (hXClosed : IsClosed X) (hYClosed : IsClosed Y)
    (hXNonempty : X.Nonempty) (hYNonempty : Y.Nonempty)
    (r s : ℕ) (hXDim : topologicalKrullDim X = (r : WithBot ℕ∞))
    (hYDim : topologicalKrullDim Y = (s : WithBot ℕ∞)) (hSum : N ≤ r + s) :
    (X ∩ Y).Nonempty ∧
      ((r + s - N : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(X ∩ Y) := by
  sorry

end AlgebraicGeometry
