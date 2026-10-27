/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Binary biproducts of cokernel coforks

Source: Stacks Project, Tag 01PJ, proof of `lemma-directed-colimit-diagram-finite-presentation`
(the finite direct sum of finitely presented modules), and Homological Algebra, Tags 0103,
0104 and 0106 (blueprint: lem-weil-pbc-biproduct-cokernel-cofork).
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- A block diagonal pair of cokernel coforks is a cokernel cofork, compatible with both
biproduct injections. Source: Stacks Project, Tag 01PJ, the finite-direct-sum sentence in
`lemma-directed-colimit-diagram-finite-presentation`; Tags 0103, 0104 and 0106 supply the
biproduct relations, additivity and cokernel universal property
(blueprint: lem-weil-pbc-biproduct-cokernel-cofork).

The block maps are Mathlib's `biprod.map`: `biprod.map_eq` identifies each with the sum
of projection, component map and injection specified in the node. Additivity is stated
using the node's zero-object and binary-biproduct formulation, equivalent to finite biproducts.

Proof:
1. The biproduct relations and bilinearity (def-weil-additive-category and
   def-weil-preadditive-category) give the four injection identities and show that the
   composite of the block maps is zero, using `w₁` and `w₂`.
2. For `f : P₁ ⊞ P₂ ⟶ T` killing the block map, restrict along each injection to obtain
   `f₁` and `f₂`. The injection identities show that `aₖ ≫ fₖ = 0`. The given cokernel
   properties supply unique factors `hₖ : Cₖ ⟶ T`. Set
   `h = biprod.fst ≫ h₁ + biprod.snd ≫ h₂`; its restrictions are `h₁` and `h₂`.
3. Expand the composite of the block projection with `h`. The two factorization
   identities and the biproduct total identity give `biprod.map c₁ c₂ ≫ h = f`.
4. Any second factor has the same restrictions by uniqueness for each given cokernel.
   The biproduct total identity and bilinearity then show that it equals `h`.
Thus the displayed projection, rather than just an isomorphic object, is a cokernel.
-/
theorem exists_isColimit_biprod_map_cokernelCofork
    {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A] [HasBinaryBiproducts A]
    {Q₁ Q₂ P₁ P₂ C₁ C₂ : A}
    (a₁ : Q₁ ⟶ P₁) (a₂ : Q₂ ⟶ P₂) (c₁ : P₁ ⟶ C₁) (c₂ : P₂ ⟶ C₂)
    (w₁ : a₁ ≫ c₁ = 0) (w₂ : a₂ ≫ c₂ = 0)
    (h₁ : IsColimit (CokernelCofork.ofπ c₁ w₁))
    (h₂ : IsColimit (CokernelCofork.ofπ c₂ w₂)) :
    ∃ w : biprod.map a₁ a₂ ≫ biprod.map c₁ c₂ = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (biprod.map c₁ c₂) w)) ∧
      (biprod.inl : Q₁ ⟶ Q₁ ⊞ Q₂) ≫ biprod.map a₁ a₂ = a₁ ≫ biprod.inl ∧
      (biprod.inr : Q₂ ⟶ Q₁ ⊞ Q₂) ≫ biprod.map a₁ a₂ = a₂ ≫ biprod.inr ∧
      (biprod.inl : P₁ ⟶ P₁ ⊞ P₂) ≫ biprod.map c₁ c₂ = c₁ ≫ biprod.inl ∧
      (biprod.inr : P₂ ⟶ P₁ ⊞ P₂) ≫ biprod.map c₁ c₂ = c₂ ≫ biprod.inr := by
  have w : biprod.map a₁ a₂ ≫ biprod.map c₁ c₂ = 0 := by
    apply biprod.hom_ext'
    · rw [biprod.inl_map_assoc, biprod.inl_map, ← Category.assoc, w₁, zero_comp,
        comp_zero]
    · rw [biprod.inr_map_assoc, biprod.inr_map, ← Category.assoc, w₂, zero_comp,
        comp_zero]
  refine ⟨w, ⟨?_, ?_⟩⟩
  · refine ⟨?_⟩
    have hl {T : A} (f : P₁ ⊞ P₂ ⟶ T) (hf : biprod.map a₁ a₂ ≫ f = 0) :
        a₁ ≫ biprod.inl ≫ f = 0 := by
      rw [← biprod.inl_map_assoc, hf, comp_zero]
    have hr {T : A} (f : P₁ ⊞ P₂ ⟶ T) (hf : biprod.map a₁ a₂ ≫ f = 0) :
        a₂ ≫ biprod.inr ≫ f = 0 := by
      rw [← biprod.inr_map_assoc, hf, comp_zero]
    refine CokernelCofork.IsColimit.ofπ _ _
      (fun f hf ↦ biprod.desc
        (h₁.desc (CokernelCofork.ofπ _ (hl f hf)))
        (h₂.desc (CokernelCofork.ofπ _ (hr f hf))))
      (fun f hf ↦ ?_) (fun f hf m hm ↦ ?_)
    · apply biprod.hom_ext'
      · rw [biprod.inl_map_assoc, biprod.inl_desc]
        exact h₁.fac (CokernelCofork.ofπ _ (hl f hf)) WalkingParallelPair.one
      · rw [biprod.inr_map_assoc, biprod.inr_desc]
        exact h₂.fac (CokernelCofork.ofπ _ (hr f hf)) WalkingParallelPair.one
    · apply biprod.hom_ext'
      · rw [biprod.inl_desc]
        apply Cofork.IsColimit.hom_ext h₁
        rw [Cofork.π_ofπ, ← Category.assoc, ← biprod.inl_map, Category.assoc, hm]
        exact (h₁.fac (CokernelCofork.ofπ _ (hl f hf)) WalkingParallelPair.one).symm
      · rw [biprod.inr_desc]
        apply Cofork.IsColimit.hom_ext h₂
        rw [Cofork.π_ofπ, ← Category.assoc, ← biprod.inr_map, Category.assoc, hm]
        exact (h₂.fac (CokernelCofork.ofπ _ (hr f hf)) WalkingParallelPair.one).symm
  · exact ⟨biprod.inl_map _ _, biprod.inr_map _ _,
      biprod.inl_map _ _, biprod.inr_map _ _⟩

end CategoryTheory.Limits
