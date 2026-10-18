/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Bases

/-! # A continuous map associated to an intersection-refining open collection

Source: Stacks Project, Topology, Tag 0D5Q, lemma-create-map-from-subcollection,
specialized to the underlying space of a scheme
(blueprint: lem-trf-derived-basis-open-subcollection-map).
-/

@[expose] public section

set_option autoImplicit false

universe u

open TopologicalSpace

namespace AlgebraicGeometry

/-- An intersection-refining collection of opens covering a scheme admits a continuous
map whose images of the collection are open, have the original opens as their inverse
images, and form a topological basis.

Source: Stacks Project, Topology, Tag 0D5Q, lemma-create-map-from-subcollection
(blueprint: lem-trf-derived-basis-open-subcollection-map).

Proof:
1. Identify two points exactly when they belong to the same members of the collection.
   Let Y be the set of equivalence classes and f the class map. Every member U is
   saturated: membership is constant on equivalence classes, so f inverse-image of
   f(U) equals U.
2. Saturation implies f(U) intersect f(V) equals f(U intersect V). Intersection
   refinement therefore expresses this intersection as the union of f(W) for members
   W contained in U intersect V. The cover hypothesis says these images cover Y.
   Declare the opens of Y to be unions of these images. The intersection formula
   verifies the topology axioms and makes the images a basis (Tag 0D5P).
3. Inverse images of these unions are unions of the corresponding original opens,
   proving continuity. The basis images are open by construction. Empty X and an
   empty collection are included: the quotient and its basis may both be empty. -/
theorem exists_continuous_map_of_open_subcollection
    (X : Scheme.{u}) (𝒞 : Set X.Opens)
    (hcover : sSup 𝒞 = ⊤)
    (hrefine : ∀ U ∈ 𝒞, ∀ V ∈ 𝒞,
      sSup {W : X.Opens | W ∈ 𝒞 ∧ W ≤ U ⊓ V} = U ⊓ V) :
    ∃ (Y : TopCat.{u}) (f : C(X, Y)),
      (∀ U ∈ 𝒞, IsOpen (f '' (U : Set X))) ∧
      (∀ U ∈ 𝒞, f ⁻¹' (f '' (U : Set X)) = (U : Set X)) ∧
      IsTopologicalBasis ((fun U : X.Opens ↦ f '' (U : Set X)) '' 𝒞) := by
  sorry

end AlgebraicGeometry
