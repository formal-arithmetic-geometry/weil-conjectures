/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Elements of coproducts of modules

The image of an element of a coproduct `∐ᵢ Nᵢ` of modules under a linear map lies in the sum of
the images of finitely many of the `Nᵢ`.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [Ring R] {ι : Type v} (N : ι → ModuleCat.{max v w} R)

/-- The image of an element of `∐ᵢ Nᵢ` under `f` lies in the sum of the images of finitely many
of the `Nᵢ`. -/
lemma exists_finset_mem_iSup_range [HasCoproduct N] {M : ModuleCat.{max v w} R} (f : ∐ N ⟶ M)
    (y : ↑(∐ N)) : ∃ S : Finset ι, f y ∈ ⨆ i ∈ S, LinearMap.range (Sigma.ι N i ≫ f).hom := by
  classical
  obtain ⟨z, rfl⟩ : ∃ z, (coprodIsoDirectSum N).inv z = y :=
    ⟨(coprodIsoDirectSum N).hom y, Iso.hom_inv_id_apply _ _⟩
  induction z using DirectSum.induction_on with
  | zero => exact ⟨∅, by simp⟩
  | of i x =>
    refine ⟨{i}, ?_⟩
    have : (coprodIsoDirectSum N).inv (DirectSum.of (fun i ↦ N i) i x) = Sigma.ι N i x :=
      congr($(lof_coprodIsoDirectSum_inv N i) x)
    rw [this]
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem (Finset.mem_singleton_self i)
      ⟨x, rfl⟩)
  | add z z' hz hz' =>
    obtain ⟨S, hS⟩ := hz
    obtain ⟨S', hS'⟩ := hz'
    refine ⟨S ∪ S', ?_⟩
    rw [map_add, map_add]
    have hle (T : Finset ι) (hT : T ⊆ S ∪ S') :
        (⨆ i ∈ T, LinearMap.range (Sigma.ι N i ≫ f).hom) ≤
          ⨆ i ∈ S ∪ S', LinearMap.range (Sigma.ι N i ≫ f).hom :=
      iSup₂_le fun i hi ↦ le_iSup₂_of_le i (hT hi) le_rfl
    exact add_mem (hle S Finset.subset_union_left hS) (hle S' Finset.subset_union_right hS')

end ModuleCat
