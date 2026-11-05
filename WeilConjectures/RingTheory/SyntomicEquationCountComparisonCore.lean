/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField

@[expose] public section
universe u v
namespace Algebra

private theorem exists_multiplier_of_localized_le
    {A : Type*} [CommRing A] (M : Submonoid A) (L : Type*)
    [CommRing L] [Algebra A L] [IsLocalization M L]
    (I J : Ideal A) (hfg : I.FG)
    (hle : I.map (algebraMap A L) ≤ J.map (algebraMap A L)) :
    ∃ s ∈ M, ∀ x ∈ I, s * x ∈ J := by
  classical
  have hkill : ∀ x ∈ I, ∃ s ∈ M, s * x ∈ J := by
    intro x hx
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff M L J x).mp
      (hle (Ideal.mem_map_of_mem _ hx))
  have hfinite : ∀ t : Finset A, (∀ x ∈ t, x ∈ I) →
      ∃ s ∈ M, ∀ x ∈ t, s * x ∈ J := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨1, M.one_mem, by simp⟩
    | @insert x t hxt ih =>
      intro ht
      obtain ⟨s, hs, hst⟩ := ih (fun y hy ↦ ht y (Finset.mem_insert_of_mem hy))
      obtain ⟨r, hr, hrx⟩ := hkill x (ht x (Finset.mem_insert_self _ _))
      refine ⟨s * r, M.mul_mem hs hr, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa only [mul_assoc] using J.mul_mem_left s hrx
      · simpa only [mul_assoc, mul_left_comm s r y] using J.mul_mem_left r (hst y hy)
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨s, hs, hst⟩ := hfinite t (fun x hx ↦ by
    rw [← ht]
    exact Submodule.subset_span hx)
  refine ⟨s, hs, ?_⟩
  intro x hx
  rw [← ht] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hst y hy
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [mul_add] using J.add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [smul_eq_mul, mul_left_comm s a x] using J.mul_mem_left a ih

end Algebra
