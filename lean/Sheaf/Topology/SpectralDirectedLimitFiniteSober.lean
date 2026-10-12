/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Order.Directed
import Sheaf.Topology.ExistsUniqueIsGenericPointOfFinite

/-!
# Spectral spaces as directed inverse limits of finite sober spaces

Source: Stacks Project, Topology, Tag 09XX, the direction from spectral spaces to limits,
using the finite images in the products of Tag 09XW
(blueprint: lem-weil-pbc-spectral-directed-limit-finite-sober).
-/

@[expose] public section

universe u

namespace Topology

/-- A spectral space is a directed inverse limit of finite sober topological spaces.
Source: Stacks Project, Topology, Tag 09XX, direction spectral implies inverse limit
(blueprint: lem-weil-pbc-spectral-directed-limit-finite-sober).

Proof:
1. Let Q be the compact open subsets of X and I the finite subsets of Q, ordered by
   inclusion. I is nonempty and directed by union. For each U in Q its characteristic
   map to the Sierpinski space W = {0,1}, with {1} open, is continuous. Let X_J be the
   image of X in W^J with the subspace topology. Coordinate restrictions give continuous
   transition maps with identity and composition laws, and the image maps p_J commute
   with them.
2. Each X_J is finite and T0: different tuples are separated by a coordinate open set.
   Thus each X_J is sober by lem-weil-pbc-finite-t0-space-sober.
3. Sobriety makes X T0. A compact open basis separates any two distinct points, so their
   images at the singleton index of a separating compact open differ. Hence the map
   to the product of the X_J is injective (def-weil-spectral-space and
   def-weil-irreducible-components).
4. A compatible family specifies one value for each coordinate U in Q. Its prescribed
   fibre is either U or its complement, closed in the constructible topology
   (def-weil-pbc-constructible-topology). Every finite intersection is nonempty because
   the corresponding tuple belongs to X_J. Compactness of the constructible topology
   (lem-weil-pbc-spectral-constructible-topology-quasi-compact) makes their full
   intersection nonempty. A point in it has precisely the prescribed family of images.
5. All p_J are continuous, so the initial topology is coarser than the topology of X.
   Conversely each compact open U is the preimage of the open coordinate value {1}
   at the singleton index {U}. Since these U form a basis (def-weil-spectral-space),
   the initial topology is the topology of X. -/
theorem exists_directed_inverseLimit_finite_sober (X : Type u)
    [tX : TopologicalSpace X] [SpectralSpace X] :
    ∃ (I : Type u) (_ : Preorder I),
      Nonempty I ∧ IsDirected I (· ≤ ·) ∧
      ∃ (Y : I → TopCat.{u}) (f : ∀ i j : I, i ≤ j → C(Y j, Y i))
        (p : ∀ i : I, C(X, Y i)),
        (∀ i : I, Finite (Y i)) ∧
        (∀ (i : I) (Z : Set (Y i)), IsIrreducible Z → IsClosed Z →
          ∃! η : Y i, IsGenericPoint η Z) ∧
        (∀ i : I, f i i le_rfl = ContinuousMap.id (Y i)) ∧
        (∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
          (f i j hij).comp (f j k hjk) = f i k (hij.trans hjk)) ∧
        (∀ (i j : I) (hij : i ≤ j), (f i j hij).comp (p j) = p i) ∧
        Function.Injective (fun x : X => fun i : I => p i x) ∧
        (∀ y : ∀ i : I, Y i,
          (∀ (i j : I) (hij : i ≤ j), f i j hij (y j) = y i) →
          ∃ x : X, ∀ i : I, p i x = y i) ∧
        tX = ⨅ i : I, TopologicalSpace.induced (p i) (Y i).str := by
  sorry

end Topology
