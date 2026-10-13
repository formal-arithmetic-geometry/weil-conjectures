/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Constant dimension neighbourhoods in a Cohen-Macaulay family

Source: Stacks Project, Tags 00RH and 0A21 (10); the local step underlying 02NM.
(blueprint: lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Local fibre dimension is a finite constant near each point of the given open.

Source: Stacks Project, Tags 00RH and 0A21 (10); the local step underlying 02NM.
Proof: Work in the source open W intersected with the inverse image of U.
Choose affine neighbourhoods of f(y) in U and y in this source open. Their ring
map R to S is flat and finitely presented. The fibre local ring at the prime q
of y is the given fibre stalk, so hdepth makes it Cohen-Macaulay. Its local
relative dimension n is a natural number, since the fibre is locally of finite
type over a field. Tag 0A21 (10) identifies this relative dimension with local
topological fibre dimension. The proof of Tag 00RH gives an open neighbourhood
of q where that relative dimension is n: after a principal shrinking choose a
quasi-finite map R[t_1,...,t_n] to S. On the fibre its target local ring is
Cohen-Macaulay and its source is regular, so the fibre map is flat (00RE).
Fibrewise flatness (00R7) gives flatness of the polynomial map at q. Openness
of flatness (00RC) gives a further principal shrinking on which it is flat.
At every point of this shrinking, base change makes the corresponding fibre
map flat and quasi-finite over polynomial n-space. The local dimension formula
therefore gives relative dimension n at every point (again 00RE).
The image O of this principal affine open is open in X, contains y, and lies
in W. Open fibre inclusions and the residue-field restriction isomorphisms
preserve local topological dimension, giving the equality for all z in O.
Only the fibre stalk at y is assumed Cohen-Macaulay; no partition is used.
(blueprint: lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood) -/
theorem exists_constant_fibre_dimension_neighbourhood_of_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] (W : X.Opens)
    (y : X) (hy : y ∈ W) (ht : f y ∈ U)
    (hdepth :
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ (n : ℕ) (O : X.Opens), y ∈ O ∧ O ≤ W ∧
      ∀ z ∈ O, topologicalKrullDimAt (f.asFiber z) = (n : WithBot ℕ∞) := by sorry

end AlgebraicGeometry
