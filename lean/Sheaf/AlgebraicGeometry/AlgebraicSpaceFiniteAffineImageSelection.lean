/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Finite affine image subcovers of a specified atlas

Source: Stacks Project, Properties of Spaces, Tags 03E4 and 03H6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finitely many affine opens of a specified atlas cover the target on field-valued
point classes. No compactness of the specified atlas is assumed.
Source: Stacks Project, Properties of Spaces, Tags 03E4 and 03H6
(blueprint: lem-trf-space-finite-affine-image-selection).

Proof: choose the compact scheme atlas Q in the hypothesis. Its continuous surjective
point map makes the target point space compact. For each affine open V of W, base change
its inclusion on any scheme test of w. The result is an open immersion followed by an
etale map, so V maps representably etale to X. Its point image is open. These images
cover: lift a target point through w, then choose an affine neighbourhood of the lift.
Compactness selects finitely many images. Enumerate them by Fin n. Equality of point
classes means equality of representatives after a common field extension, exactly the
condition IsJointlySurjective: take a common extension of the field of the fixed target
representative and the source representative and restrict the latter section to it.
The common-field relation is transitive by amalgamating fields over the intervening
field, so equality in the quotient suffices. If W is empty, select the empty family:
surjectivity of w
forces the target to have no field-valued points. This also proves the stated empty-case
condition without requiring the chosen opens to be disjoint. -/
theorem exists_finite_affine_image_selection {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : ∃ (Q : Over S) (q : yoneda.obj Q ⟶ X.obj.obj),
      CompactSpace Q.left ∧ IsEtale q ∧ IsSurjective q)
    (W : Over S) (w : yoneda.obj W ⟶ X.obj.obj)
    (hw : IsEtale w) (hs : IsSurjective w) :
    ∃ (n : ℕ) (V : Fin n → W.left.Opens),
      (∀ i : Fin n, IsAffineOpen (V i)) ∧
      IsJointlySurjective (fun i : Fin n ↦
        yoneda.map (Over.homMk (U := Over.mk ((V i).ι ≫ W.hom))
          (V := W) (V i).ι rfl) ≫ w) ∧
      (IsEmpty W.left → n = 0) := by sorry

end AlgebraicGeometry.AlgebraicSpace
