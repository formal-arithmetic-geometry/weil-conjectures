/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Derivations and squares of ideals

A derivation maps the square of an ideal into the ideal itself.  Applying this to a family of
derivations gives the linear-algebra step of the Jacobian criterion: relations lying in a prime
`Q` whose Jacobian determinant avoids `Q` admit no nontrivial relation modulo `Q ^ 2`.

## Main results

* `Derivation.mem_smul_top_of_mem_sq`: a derivation with values in `M` maps `I ^ 2` into
  `I • (⊤ : Submodule A M)`.
* `Derivation.mem_of_mem_sq`: a derivation of `A` maps `I ^ 2` into `I`.
* `Ideal.mem_of_sum_mul_mem_sq_of_det_notMem`: if the relations `rel` lie in a prime `Q` and their
  Jacobian determinant with respect to a family of derivations avoids `Q`, then every relation
  `∑ bᵢ relᵢ ∈ Q ^ 2` has all its coefficients `bᵢ` in `Q`.
-/

@[expose] public section

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M]

/-- A derivation maps `I ^ 2` into `I • ⊤`. -/
theorem mem_smul_top_of_mem_sq (D : Derivation R A M) (I : Ideal A) {x : A} (hx : x ∈ I ^ 2) :
    D x ∈ I • (⊤ : Submodule A M) := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) fun y z hy hz ↦ ?_
  -- the Leibniz rule writes `D (y * z)` as a combination of `D y` and `D z`
  -- with coefficients in `I`
  · rw [D.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hy Submodule.mem_top)
      (Submodule.smul_mem_smul hz Submodule.mem_top)
  · simpa using Submodule.add_mem _ hy hz

/-- A derivation of `A` maps `I ^ 2` into `I`. -/
theorem mem_of_mem_sq (D : Derivation R A A) (I : Ideal A) {x : A} (hx : x ∈ I ^ 2) : D x ∈ I := by
  refine Submodule.smul_le.2 (fun r hr m _ ↦ ?_) (D.mem_smul_top_of_mem_sq I hx)
  rw [smul_eq_mul]
  exact I.mul_mem_right m hr

end Derivation

/-- **The linear-algebra step of the Jacobian criterion.**  Let `Q` be a prime of `A` containing
the relations `rel`, and suppose that the determinant of the Jacobian matrix of `rel` with respect
to a family `D` of derivations is not in `Q`.  Then `∑ bᵢ relᵢ ∈ Q ^ 2` forces every `bᵢ` to lie
in `Q`. -/
theorem Ideal.mem_of_sum_mul_mem_sq_of_det_notMem {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (Q : Ideal A) [Q.IsPrime] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (D : σ → Derivation R A A) (rel : σ → A) (hrel : ∀ i, rel i ∈ Q)
    (hdet : (Matrix.of fun j i ↦ D j (rel i)).det ∉ Q)
    (b : σ → A) (hz : ∑ i, b i * rel i ∈ Q ^ 2) (i : σ) : b i ∈ Q := by
  have key : ∀ j : σ, ∑ i, b i * D j (rel i) ∈ Q := by
    intro j
    have h1 : D j (∑ i, b i * rel i) ∈ Q := (D j).mem_of_mem_sq Q hz
    have h2 : ∑ i, rel i * D j (b i) ∈ Q :=
      Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_right _ _ (hrel i)
    have h3 : ∑ i, b i * D j (rel i)
        = D j (∑ i, b i * rel i) - ∑ i, rel i * D j (b i) := by
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
    rw [h3]
    exact Ideal.sub_mem _ h1 h2
  set M : Matrix σ σ (A ⧸ Q) := (Matrix.of fun j i ↦ D j (rel i)).map (Ideal.Quotient.mk Q) with hM
  have hdetM : M.det ≠ 0 := by
    have hmap : M.det = Ideal.Quotient.mk Q (Matrix.of fun j i ↦ D j (rel i)).det :=
      (RingHom.map_det (Ideal.Quotient.mk Q) _).symm
    rw [hmap]
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hdet
  have hw : M.mulVec (fun i ↦ Ideal.Quotient.mk Q (b i)) = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.map_apply, Matrix.of_apply,
      Pi.zero_apply, ← map_mul, ← map_sum, Ideal.Quotient.eq_zero_iff_mem]
    simpa only [mul_comm] using key j
  simpa only [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] using
    congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdetM hw) i
