/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-! # Values of the exterior pairing on dual families

Mathlib deprecated `exteriorPower.pairingDual_apply_apply_eq_one` and
`exteriorPower.pairingDual_apply_apply_eq_one_zero` without replacement (2026-08-23). The Koszul
top-homology files (`KoszulCoefficientTopHomology`, `KoszulConormalTopHomologyPos`) use them, so
this file keeps the two statements, with Mathlib's proofs
(`Mathlib.LinearAlgebra.ExteriorPower.Pairing`), under `WeilConjectures.ExteriorPower`.
-/

@[expose] public section

namespace WeilConjectures.ExteriorPower

open exteriorPower

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} [LinearOrder ι]
  (x : ι → M) (f : ι → Module.Dual R M)
  (h₁ : ∀ i, f i (x i) = 1) (h₀ : ∀ ⦃i j⦄, i ≠ j → f i (x j) = 0) (n : ℕ)

include h₁ h₀ in
/-- The exterior pairing of the wedge of the `f (a i)` with the wedge of the `x (a i)` is `1`. -/
lemma pairingDual_apply_apply_eq_one (a : Fin n ↪o ι) :
    pairingDual R M n (ιMulti _ _ (f ∘ a)) (ιMulti _ _ (x ∘ a)) = 1 := by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply]
  rw [← Matrix.det_one (n := Fin n)]
  congr
  ext i j
  dsimp
  by_cases hij : i = j
  · subst hij
    simp only [h₁, Matrix.one_apply_eq]
  · rw [h₀ (by simpa using Ne.symm hij), Matrix.one_apply_ne hij]

include h₀ in
/-- The exterior pairing of the wedge of the `f (a i)` with the wedge of the `x (b i)` is `0`
for distinct order embeddings `a ≠ b`. -/
lemma pairingDual_apply_apply_eq_one_zero (a b : Fin n ↪o ι) (h : a ≠ b) :
    pairingDual R M n (ιMulti _ _ (f ∘ a)) (ιMulti _ _ (x ∘ b)) = 0 := by
  simp only [pairingDual_ιMulti_ιMulti, Function.comp_apply, Matrix.det_apply]
  refine Finset.sum_eq_zero (fun σ _ ↦ ?_)
  simp only [Matrix.of_apply, smul_eq_iff_eq_inv_smul, smul_zero]
  by_contra h'
  apply h
  have : a = b ∘ σ := by
    ext i
    by_contra hi
    exact h' (Finset.prod_eq_zero (i := i) (by simp) (h₀ hi))
  have hσ : Monotone σ := fun i j hij ↦ by
    have h'' := congr_fun this
    dsimp at h''
    rw [← a.map_rel_iff] at hij
    simpa only [← b.map_rel_iff, ← h'']
  have hσ' : Monotone σ.symm := fun i j hij ↦ by
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    simp only [Equiv.symm_apply_apply]
    by_contra! h
    obtain rfl : i = j := σ.injective (le_antisymm hij (hσ h.le))
    simp only [lt_self_iff_false] at h
  obtain rfl : σ = 1 := by
    ext i : 1
    congrm $(Subsingleton.elim (σ.toOrderIso hσ hσ') (OrderIso.refl _)) i
  ext
  apply congr_fun this

end WeilConjectures.ExteriorPower
