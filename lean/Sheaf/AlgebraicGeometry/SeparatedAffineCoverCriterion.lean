/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Separatedness from an affine open cover with affine overlaps

Source: literature/stacks-project/schemes.tex, Schemes, Lemma Tag 01KP (2)
(blueprint: lem-weil-pbc-separated-affine-cover-criterion)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u v

/-- An affine open cover with affine overlaps and surjective restriction products
makes a morphism to an affine scheme separated.
Source: Schemes, Lemma Tag 01KP (2) (blueprint: lem-weil-pbc-separated-affine-cover-criterion).
Proof (Stacks 01KP (2), specialized to the affine base), following the node:
1. Write S = Spec R, A_a = Γ(V, V_a), and C_ab = Γ(V, V_a ∩ V_b). The opens
   W_ab = p⁻¹(V_a) ∩ q⁻¹(V_b) cover V ×_S V: choose cover members for each projection
   of a point. By `lem-weil-pbc-open-fibre-product` and
   `lem-weil-pbc-fibre-product-affine-spectra`, W_ab is V_a ×_S V_b, hence affine with
   section ring A_a ⊗[R] A_b. The projections induce x ↦ x ⊗ 1 and y ↦ 1 ⊗ y
   (`def-pc-fibre-product`, `def-weil-affine-spectrum`).
2. Both projections composed with the diagonal are the identity. Thus its inverse
   image of W_ab is V_a ∩ V_b, affine by hypothesis, with ring C_ab
   (`def-weil-proper-morphism`, `def-pc-fibre-product`).
3. Functoriality of section pullback identifies the diagonal's induced ring map
   φ_ab : A_a ⊗[R] A_b → C_ab with x ⊗ y ↦ x| · y|: it has this value on x ⊗ 1
   and 1 ⊗ y, hence on their product; pure tensors additively generate the tensor ring.
4. The canonical map A_a ⊗[ℤ] A_b → A_a ⊗[R] A_b is surjective since its image
   contains every pure tensor. Its composite with φ_ab is the assumed surjective map,
   so φ_ab is surjective.
5. Apply `lem-weil-pbc-closed-immersion-affine-cover-criterion` (2) to the diagonal
   and the cover W_ab: each inverse image is affine and each induced section map is
   surjective. The diagonal is a closed immersion (`def-weil-closed-immersion`),
   which is exactly separatedness (`def-weil-proper-morphism`). -/
theorem separated_of_affine_open_cover
    {S V : Scheme.{u}} [IsAffine S]
    (f : V ⟶ S) (A : Type v) (Vₐ : A → V.Opens)
    (hcover : ⋃ a, (Vₐ a : Set V) = Set.univ)
    (haff : ∀ a, IsAffineOpen (Vₐ a))
    (haffint : ∀ a b, IsAffineOpen (Vₐ a ⊓ Vₐ b))
    (hsurj : ∀ (a b : A),
      ∃ φ : TensorProduct ℤ (Γ(V, Vₐ a)) (Γ(V, Vₐ b)) →+* Γ(V, Vₐ a ⊓ Vₐ b),
        Function.Surjective φ ∧
          ∀ (x : Γ(V, Vₐ a)) (y : Γ(V, Vₐ b)),
            φ (TensorProduct.tmul ℤ x y) =
              (V.presheaf.map (homOfLE inf_le_left).op) x *
                (V.presheaf.map (homOfLE inf_le_right).op) y) :
    IsSeparated f := by
  sorry

end AlgebraicGeometry
