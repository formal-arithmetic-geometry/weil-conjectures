/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ClosedPointOfAffineOpen
import Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.RingTheory.InfiniteSetOfIsMaximalOfRingKrullDimPos

/-!
# Infinitely many closed points in a positive-dimensional irreducible closed subset

Source: Stacks Project, Varieties, Tags 0478 and 0A21, with the affine positive-dimension
argument in Algebra (blueprint: lem-sc-positive-dimensional-locally-algebraic-closed-points).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An irreducible closed subset of positive topological Krull dimension in a scheme locally
of finite type over a field contains infinitely many ambient closed points. Source: Stacks
Project, Varieties, Tags 0478 and 0A21, and the affine positive-dimension argument in Algebra
(blueprint: lem-sc-positive-dimensional-locally-algebraic-closed-points).

Proof:
1. Give `Z` its reduced induced closed subscheme structure using
   `lem-weil-pbc-reduced-induced-closed-subscheme`. Its closed immersion into `X` makes it
   locally of finite type over `k`. Choose an affine open `U = Spec R` meeting `Z`.
   The intersection `V = U ∩ Z` is `Spec A`, where `A = R/I` for the radical ideal defining
   `V`. Irreducibility makes `I` prime, so `A` is a finite type domain over `k`.
   By `lem-sc-dimension-locally-algebraic` (Tag 0A21), the nonempty open `V` has the same
   positive dimension as `Z`, so `A` has positive ring Krull dimension.
2. Apply `lem-sc-fg-domain-positive-dimension-infinite-maximals` to `A`. Its infinitely many
   maximal ideals give distinct closed points of `V`; their inverse images in `R` are
   maximal ideals and thus give closed points of `U`.
3. By `lem-sc-affine-maximal-points-closed-in-lft-scheme` (Tag 0478), each of these points
   is closed in `X`. All lie in `Z`, so `Z ∩ closedPoints X` is infinite. -/
theorem infinite_closedPoints_inter_of_topologicalKrullDim_pos
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (Z : Set X) (hZclosed : IsClosed Z) (hZirred : IsIrreducible Z)
    (hZdim : 0 < topologicalKrullDim Z) :
    (Z ∩ closedPoints X).Infinite := by
  sorry

end AlgebraicGeometry
