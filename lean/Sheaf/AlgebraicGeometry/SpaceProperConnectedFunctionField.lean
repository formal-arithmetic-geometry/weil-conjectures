/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Mathlib.Algebra.Field.IsField
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Connected.Basic

/-! # Global functions on a proper reduced connected algebraic space

Source: Stacks Project, Spaces over Fields, Tag 0DMY,
lemma-proper-geometrically-reduced-global-sections, clauses (1)--(3)
(blueprint: lem-sfb-space-proper-connected-function-field).

Global functions are compatible regular functions on the existing small affine etale
model. The scalar action is multiplication by the canonical pullback of base scalars.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Global functions on a proper reduced nonempty connected algebraic space form a
field finite-dimensional over the base field. Reducedness and connectedness are ordinary,
without geometric hypotheses; the resulting field need not equal the base field.

Source: Stacks Project, Spaces over Fields, Tag 0DMY,
lemma-proper-geometrically-reduced-global-sections, clauses (1)--(3)
(blueprint: lem-sfb-space-proper-connected-function-field).

Proof:
1. Apply lem-sfb-space-proper-global-algebra-components. It identifies the global-functions
   algebra with the product of the algebras on connected components, proves finite
   dimensionality over k, and makes each factor a finite field extension when X is reduced.
   Restriction to the existing affine etale basis computes the same structure-sheaf
   global functions; its scalar map is affineGlobalScalar.
2. Nonempty connectedness makes the whole point space its unique connected component:
   every maximal nonempty connected subset must equal the whole connected space.
   Evaluation on this sole component identifies the product with its one field factor.
   Transporting the field property and finite dimensionality gives both conclusions. -/
theorem globalFunctions_isField_finite_of_proper_reduced_connected
    (k : Type u) [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hf : MapIsProper f) (hred : X.IsReduced)
    [ConnectedSpace (Point X.obj.obj)] :
    IsField (RingCat.sectionsSubring X.smallStructureRings.obj) ∧
      @Module.Finite k (RingCat.sectionsSubring X.smallStructureRings.obj) _ _
        (affineGlobalScalar k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
          (Iso.refl _) X f).toModule := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
