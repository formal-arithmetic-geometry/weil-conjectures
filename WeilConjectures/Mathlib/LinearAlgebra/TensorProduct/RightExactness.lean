/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Exactness after tensoring with a retract

If a sequence stays exact after tensoring with a module `P`, it stays exact after tensoring with
every retract `M` of `P`, for instance with `M` when `P = N × M`.
-/

@[expose] public section

open TensorProduct


namespace Function.Exact

variable {R : Type*} [CommRing R] {C₀ C₁ C₂ M P : Type*} [AddCommGroup C₀] [AddCommGroup C₁]
  [AddCommGroup C₂] [AddCommGroup M] [AddCommGroup P] [Module R C₀] [Module R C₁] [Module R C₂]
  [Module R M] [Module R P]

omit [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂] [AddCommGroup M] [AddCommGroup P]
  [Module R C₀] [Module R C₁] [Module R C₂] [Module R M] [Module R P] in
private lemma lTensor_rTensor_comm {Q Q' D D' : Type*} [AddCommGroup Q] [AddCommGroup Q']
    [Module R Q] [Module R Q'] (φ : Q →ₗ[R] Q') [AddCommGroup D] [AddCommGroup D'] [Module R D]
    [Module R D'] (d : D →ₗ[R] D') (x : Q ⊗[R] D) :
    d.lTensor Q' (φ.rTensor D x) = φ.rTensor D' (d.lTensor Q x) := by
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.comp_apply]

/-- **Exactness after tensoring passes to retracts.** If `d₀, d₁` stay exact after tensoring
with `P` and `M` is a retract of `P`, they stay exact after tensoring with `M`. -/
lemma rTensor_of_retract {d₀ : C₀ →ₗ[R] C₁} {d₁ : C₁ →ₗ[R] C₂} (i : M →ₗ[R] P)
    (r : P →ₗ[R] M) (hri : r ∘ₗ i = LinearMap.id)
    (h : Function.Exact (d₀.lTensor P) (d₁.lTensor P)) :
    Function.Exact (d₀.lTensor M) (d₁.lTensor M) := by
  have hr (x : M ⊗[R] C₁) : r.rTensor C₁ (i.rTensor C₁ x) = x := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hri, LinearMap.rTensor_id,
      LinearMap.id_apply]
  have hr₂ (x : M ⊗[R] C₂) : r.rTensor C₂ (i.rTensor C₂ x) = x := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hri, LinearMap.rTensor_id,
      LinearMap.id_apply]
  intro x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (h (i.rTensor C₁ x)).mp (by rw [lTensor_rTensor_comm, hx, map_zero])
    refine ⟨r.rTensor C₀ z, ?_⟩
    rw [lTensor_rTensor_comm, hz, hr]
  · rintro ⟨z, rfl⟩
    have h0 : d₁.lTensor P (d₀.lTensor P (i.rTensor C₀ z)) = 0 :=
      (h _).mpr ⟨_, rfl⟩
    rw [← hr₂ (d₁.lTensor M (d₀.lTensor M z)), ← lTensor_rTensor_comm i d₁,
      ← lTensor_rTensor_comm i d₀, h0, map_zero]

end Function.Exact
