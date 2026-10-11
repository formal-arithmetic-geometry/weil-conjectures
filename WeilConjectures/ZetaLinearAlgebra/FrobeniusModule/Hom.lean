/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Trace
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace

/-!
# Traces on spaces of linear maps between Frobenius modules

If a Frobenius module `P` is identified with the space of linear maps `A → B` between two
Frobenius modules, its Frobenius becoming `φ ↦ F_B ∘ φ ∘ F_A⁻¹`, then the trace of `F_Pᵏ` is
`tr (F_Bᵏ) · tr (F_A⁻ᵏ)`. For the dual `A = M^∨` the inverse Frobenius `F_A⁻¹` is the transpose
of `F_M`, with the same traces of powers as `F_M`.

## Main results

- `FrobeniusModule.trace_frobeniusEnd_pow_eq_mul_of_linearEquiv`: the trace on `Hom(A, B)`.
- `FrobeniusModule.trace_dual_frobenius_symm_pow`: `tr (F_{M^∨}⁻ᵏ) = tr (F_Mᵏ)`.
-/

@[expose] public section

universe u v t w

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- Conjugation by a linear isomorphism commutes with powers. -/
private lemma conj_pow {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (e : V ≃ₗ[K] W) (f : Module.End K V) (k : ℕ) :
    e.conj f ^ k = e.conj (f ^ k) := by
  induction k with
  | zero => ext x; simp [LinearEquiv.conj_apply]
  | succ k ih => rw [pow_succ, ih, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearEquiv.conj_comp]

/-- If `P ≅ Hom(A, B)` with the Frobenius of `P` becoming `φ ↦ F_B ∘ φ ∘ F_A⁻¹`, then
`tr (F_Pᵏ) = tr (F_Bᵏ) · tr (F_A⁻ᵏ)`. -/
theorem trace_frobeniusEnd_pow_eq_mul_of_linearEquiv (P : FrobeniusModule.{u, v} K)
    (A : FrobeniusModule.{t, v} K) (B : FrobeniusModule.{w, v} K)
    (E : P.carrier ≃ₗ[K] (A.carrier →ₗ[K] B.carrier))
    (hE : ∀ d, E (P.frobenius d) = B.frobeniusEnd ∘ₗ E d ∘ₗ A.frobenius.symm.toLinearMap)
    (k : ℕ) :
    LinearMap.trace K _ (P.frobeniusEnd ^ k) =
      LinearMap.trace K _ (B.frobeniusEnd ^ k) *
        LinearMap.trace K _ (A.frobenius.symm.toLinearMap ^ k) := by
  set C : Module.End K (A.carrier →ₗ[K] B.carrier) :=
    LinearMap.llcomp K A.carrier B.carrier B.carrier B.frobeniusEnd ∘ₗ
      LinearMap.lcomp K B.carrier A.frobenius.symm.toLinearMap
  have hC : E.conj P.frobeniusEnd = C := by
    refine LinearMap.ext fun φ ↦ ?_
    obtain ⟨d, rfl⟩ := E.surjective φ
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact (hE d).trans rfl
  have hCk : C ^ k = LinearMap.llcomp K A.carrier B.carrier B.carrier (B.frobeniusEnd ^ k) ∘ₗ
      LinearMap.lcomp K B.carrier (A.frobenius.symm.toLinearMap ^ k) := by
    induction k with
    | zero => ext φ x; simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ B.frobeniusEnd, pow_succ' A.frobenius.symm.toLinearMap]
      ext φ x
      simp [C, Module.End.mul_apply]
  rw [← LinearMap.trace_conj' _ E, ← conj_pow, hC, hCk, LinearMap.trace_llcomp_comp_lcomp]

/-- The inverse Frobenius of an isomorphic Frobenius module has the same traces of powers. -/
theorem Equiv.trace_frobenius_symm_pow {M : FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{u, v} K} (e : M.Equiv N) (k : ℕ) :
    LinearMap.trace K _ (N.frobenius.symm.toLinearMap ^ k) =
      LinearMap.trace K _ (M.frobenius.symm.toLinearMap ^ k) := by
  have h : N.frobenius.symm.toLinearMap = e.toLinearEquiv.conj M.frobenius.symm.toLinearMap := by
    refine LinearMap.ext fun y ↦ ?_
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq, <- e.map_frobenius, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  rw [h, conj_pow, LinearMap.trace_conj']

/-- The inverse of the Frobenius of the dual `M^∨` is the transpose of the Frobenius of `M`, so
it has the same traces of powers. -/
theorem trace_dual_frobenius_symm_pow (M : FrobeniusModule.{u, v} K) (k : ℕ) :
    LinearMap.trace K _ (M.dual.frobenius.symm.toLinearMap ^ k) =
      LinearMap.trace K _ (M.frobeniusEnd ^ k) := by
  have h1 : M.dual.frobenius.symm.toLinearMap = Module.Dual.transpose (R := K) M.frobeniusEnd := by
    refine LinearMap.ext fun (f : Module.Dual K M.carrier) ↦ ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
    refine LinearMap.ext fun x ↦ ?_
    rw [dual_frobenius_apply, LinearMap.comp_apply]
    exact congrArg f (M.frobenius.apply_symm_apply x).symm
  have h2 : ∀ j : ℕ, Module.Dual.transpose (R := K) M.frobeniusEnd ^ j =
      Module.Dual.transpose (R := K) (M.frobeniusEnd ^ j) := fun j ↦ by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ, ih, pow_succ']
      rfl
  rw [h1, h2]
  exact LinearMap.trace_transpose' _

end FrobeniusModule
