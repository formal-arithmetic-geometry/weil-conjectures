/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Separatedness from an affine open cover with affine overlaps

## References

* [Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u v

/-- An affine open cover with affine overlaps and surjective restriction products
makes a morphism to an affine scheme separated. -/
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
  have hcov : TopologicalSpace.IsOpenCover Vₐ := by
    change iSup Vₐ = ⊤
    simpa only [← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_iSup,
      TopologicalSpace.Opens.coe_top] using hcover
  have hsep : V.IsSeparated := by
    apply Scheme.isSeparated_of_isSeparatingPair Vₐ hcov haff haffint
    intro a b
    obtain ⟨φ, hφ, htmul⟩ := hsurj a b
    unfold IsSeparatingPair
    apply top_unique
    intro z hz
    obtain ⟨t, ht⟩ := hφ ((Vₐ a ⊓ Vₐ b).topIso.hom z)
    have hmem : ∀ t, (Vₐ a ⊓ Vₐ b).topIso.inv (φ t) ∈
        Subring.closure
          (Set.range ⇑(V.homOfLE (inf_le_left : Vₐ a ⊓ Vₐ b ≤ Vₐ a)).appTop.hom ∪
            Set.range ⇑(V.homOfLE (inf_le_right : Vₐ a ⊓ Vₐ b ≤ Vₐ b)).appTop.hom) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        rw [htmul, map_mul]
        apply Subring.mul_mem
        · rw [← Scheme.homOfLE_appTop_topIso_inv inf_le_left]
          exact Subring.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)
        · rw [← Scheme.homOfLE_appTop_topIso_inv inf_le_right]
          exact Subring.subset_closure (Set.mem_union_right _ ⟨_, rfl⟩)
      | add x y hx hy =>
        simpa only [map_add] using Subring.add_mem _ hx hy
    simpa only [ht, CommRingCat.inv_hom_apply] using hmem t
  infer_instance

end AlgebraicGeometry
