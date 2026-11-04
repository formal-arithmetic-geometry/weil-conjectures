/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite sums of morphisms of short complexes

The components of a finite sum of morphisms of short complexes are the sums of the
components.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Preadditive C] {S₁ S₂ : ShortComplex C}

@[simp]
lemma sum_τ₁ {J : Type*} (s : Finset J) (φ : J → (S₁ ⟶ S₂)) :
    (∑ j ∈ s, φ j).τ₁ = ∑ j ∈ s, (φ j).τ₁ :=
  map_sum (AddMonoidHom.mk' (fun φ : S₁ ⟶ S₂ ↦ φ.τ₁) fun _ _ ↦ rfl) φ s

@[simp]
lemma sum_τ₂ {J : Type*} (s : Finset J) (φ : J → (S₁ ⟶ S₂)) :
    (∑ j ∈ s, φ j).τ₂ = ∑ j ∈ s, (φ j).τ₂ :=
  map_sum (AddMonoidHom.mk' (fun φ : S₁ ⟶ S₂ ↦ φ.τ₂) fun _ _ ↦ rfl) φ s

@[simp]
lemma sum_τ₃ {J : Type*} (s : Finset J) (φ : J → (S₁ ⟶ S₂)) :
    (∑ j ∈ s, φ j).τ₃ = ∑ j ∈ s, (φ j).τ₃ :=
  map_sum (AddMonoidHom.mk' (fun φ : S₁ ⟶ S₂ ↦ φ.τ₃) fun _ _ ↦ rfl) φ s

end CategoryTheory.ShortComplex
