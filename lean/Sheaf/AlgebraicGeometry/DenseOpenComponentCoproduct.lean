/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties

/-! # A component coproduct over prescribed dense opens -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The component coproduct is an isomorphism on a dense open whose inverse image in
 each component lies in any prescribed dense open.
Source: Stacks Project, Morphisms, Tag 0BAJ, the reduction to disjoint components;
the explicit component-open argument of
`lem-weil-pbc-dense-open-component-modifications`, steps 1 and 2.

Proof: Put Z i = range (ι i). Remove the union of the Z j for j ≠ i to get W i.
The union is closed because the family is finite. The generic point of Z i is
outside every other component by maximality and distinctness, so W i contains it.
The components cover X, hence W i is contained in Z i. The closed immersion ι i
restricted to W i is surjective onto a reduced scheme, and is therefore an
isomorphism: its ideal on each affine lies in the nilradical, which is zero.
Transfer V i intersected with the inverse image of W i across this isomorphism
and include the image as an open O i of X. A dense open of the integral C i
contains its generic point, so O i contains the generic point of Z i.
The O i are disjoint. Their union U is dense because its closure contains each
component, and the components cover X. The inverse image of U in C i is exactly
the inverse image of O i and lies in V i. The maps from these inverse images to
O i are isomorphisms; their coproduct is an isomorphism onto U, identified with
the restriction of Sigma.desc ι by base change of a scheme coproduct.
For an empty family the covering hypothesis forces X empty, and U is empty.
(blueprint: lem-weil-pbc-dense-open-component-coproduct) -/
theorem exists_dense_open_component_coproduct
    (X : Scheme.{u}) [IsReduced X]
    (n : ℕ) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hC : ∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
      Set.range (ι i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i ↦ Set.range (ι i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z)
    (V : ∀ i, (C i).Opens) (hV : ∀ i, Dense (V i : Set (C i))) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (CategoryTheory.Limits.Sigma.desc ι ∣_ U) ∧
      ∀ i, ι i ⁻¹ᵁ U ≤ V i := by sorry

end AlgebraicGeometry
