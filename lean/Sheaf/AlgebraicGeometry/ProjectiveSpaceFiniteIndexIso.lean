/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # Reindexing finite projective space and its twisting module

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-finite-index-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- A nonempty finite coordinate type can be replaced by `ULift (Fin (n + 1))`,
compatibly with the structure map and the twisting module.

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-finite-index-iso).

Proof:
1. Let n + 1 be the cardinality of the finite nonempty type, and choose a bijection
   between it and ULift (Fin (n + 1)). Rename polynomial variables by this bijection.
   The resulting graded ring isomorphism preserves the degree and the base ring.
2. On each standard open it gives an isomorphism of the degree-zero localized rings,
   carrying each coordinate ratio to the renamed ratio. These isomorphisms agree on
   overlaps, since localization commutes with the renaming and its inverse.
3. Glue the affine scheme isomorphisms; their composites are identities chartwise.
   They preserve the constant-ring maps, so the structure morphism is unchanged.
4. On the same opens identify the rank-one twisting modules by sending the basis
   indexed by one coordinate to the basis indexed by its renamed coordinate. Their
   transition units are precisely the coordinate ratios, which step 2 preserves.
   Thus the local identifications glue to the asserted pullback isomorphism.
   Equivalently this is the base change of the renaming on the integral model. -/
theorem exists_finite_index_iso (β : Type u) [Finite β] [Nonempty β] (S : Scheme.{u}) :
    ∃ (n : ℕ) (e : ℙ(β; S) ≅ ℙ(ULift.{u} (Fin (n + 1)); S)),
      e.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = ℙ(β; S) ↘ S ∧
      Nonempty ((Scheme.Modules.pullback e.hom).obj
        (twist (ULift.{u} (Fin (n + 1))) S 1) ≅ twist β S 1) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
