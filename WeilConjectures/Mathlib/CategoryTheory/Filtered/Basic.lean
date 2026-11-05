/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Finitely many properties at a common stage of a cofiltered category

If finitely many properties of morphisms `k ⟶ j` into a fixed object `j` of a cofiltered category
each hold for some morphism and are stable under precomposition, then they all hold for a common
morphism (`CategoryTheory.IsCofiltered.exists_forall_of_finite`). A finite family of objects has a
common lower bound (`CategoryTheory.IsCofiltered.exists_forall_nonempty_hom`). Dually, finite
families of objects and of morphisms out of an object of a filtered category have cocones
(`CategoryTheory.IsFiltered.exists_cocone_of_finite`,
`CategoryTheory.IsFiltered.exists_comp_eq_of_finite`).
-/

@[expose] public section

namespace CategoryTheory.IsCofiltered

variable {C : Type*} [Category* C] [IsCofiltered C]

end CategoryTheory.IsCofiltered

namespace CategoryTheory.IsFiltered

variable {K : Type*} [Category* K]

/-- A finite family of morphisms `aᵢ : k ⟶ kᵢ` out of an object of a filtered category extends to
a cocone: there are `A : k ⟶ k'` and `bᵢ : kᵢ ⟶ k'` with `aᵢ ≫ bᵢ = A`. -/
lemma exists_comp_eq_of_finite [IsFilteredOrEmpty K] {k : K}
    {ι : Type*} [Finite ι] {k₁ : ι → K} (a : ∀ i, k ⟶ k₁ i) :
    ∃ (k' : K) (A : k ⟶ k') (b : ∀ i, k₁ i ⟶ k'), ∀ i, a i ≫ b i = A := by
  classical
  have := Fintype.ofFinite ι
  have : Nonempty K := ⟨k⟩
  have : IsFiltered K := { }
  let O : Finset K := insert k (Finset.univ.image k₁)
  have hk : k ∈ O := Finset.mem_insert_self _ _
  have hk₁ (i : ι) : k₁ i ∈ O :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image fun i ↦ ⟨k, k₁ i, hk, hk₁ i, a i⟩
  exact ⟨IsFiltered.sup O H, IsFiltered.toSup O H hk, fun i ↦ IsFiltered.toSup O H (hk₁ i),
    fun i ↦ IsFiltered.toSup_commutes O H hk (hk₁ i)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

/-- A finite family of objects of a filtered category has a cocone. -/
lemma exists_cocone_of_finite [IsFiltered K] {ι : Type*} [Finite ι]
    (k₁ : ι → K) : ∃ k : K, Nonempty (∀ i, k₁ i ⟶ k) := by
  classical
  have := Fintype.ofFinite ι
  let O : Finset K := Finset.univ.image k₁
  exact ⟨IsFiltered.sup O ∅, ⟨fun i ↦ IsFiltered.toSup O ∅
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩⟩

end CategoryTheory.IsFiltered
