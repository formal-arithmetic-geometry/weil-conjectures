/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed

/-!
# The invariant matrix algebra and its scalar-extension map

For a map `b` from the absolute Galois group of `K` to `GLₙ(Kˢᵉᵖ)`, the `K`-subalgebra of
matrices invariant under the twisted conjugation `M ↦ b(g) g(M) b(g)⁻¹`, and the scalar extension
map from `Kˢᵉᵖ ⊗ (invariants)` to the full matrix algebra.

## References

* [Stacks Project, Tags 03R6 and 03R7](https://stacks.math.columbia.edu/tag/03R7)
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

variable (K : Type u) [Field K] (n : ℕ)
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))

/-- The subalgebra of matrices `M` with `b(g) g(M) b(g)⁻¹ = M` for all Galois elements `g`. -/
noncomputable def matrixDescentInvariants :
    Subalgebra K (Matrix (Fin n) (Fin n) (SeparableClosure K)) where
  carrier := {M | ∀ g, (b g).val * M.map g * ((b g)⁻¹).val = M}
  zero_mem' := by intro g; simp
  one_mem' := by intro g; simp
  add_mem' := by
    intro M N hM hN g
    change (b g).val * (g.toAlgHom.mapMatrix (M + N)) * ((b g)⁻¹).val = M + N
    rw [map_add, mul_add, add_mul]
    exact congrArg₂ (· + ·) (hM g) (hN g)
  mul_mem' := by
    intro M N hM hN g
    change (b g).val * (g.toAlgHom.mapMatrix (M * N)) * ((b g)⁻¹).val = M * N
    rw [map_mul]
    calc
      _ = ((b g).val * M.map g * ((b g)⁻¹).val) *
          ((b g).val * N.map g * ((b g)⁻¹).val) := by simp [mul_assoc]
      _ = M * N := by rw [hM g, hN g]
  algebraMap_mem' := by
    intro k g
    change (b g).val * (g.toAlgHom.mapMatrix (algebraMap K _ k)) * ((b g)⁻¹).val = _
    rw [AlgHom.commutes, ← Algebra.commutes]
    simp [mul_assoc]

/-- Scalar extension of the invariant subalgebra, explicitly `l ⊗ a ↦ l • a`. -/
noncomputable def matrixDescentScalarMap :
    (SeparableClosure K ⊗[K] matrixDescentInvariants K n b) →ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (matrixDescentInvariants K n b).val
    (fun l a ↦ Algebra.commutes l (a : Matrix (Fin n) (Fin n) (SeparableClosure K)))

/-- The scalar extension map sends `1 ⊗ a` to `a`. -/
@[simp] theorem matrixDescentScalarMap_one_tmul (a : matrixDescentInvariants K n b) :
    matrixDescentScalarMap K n b (1 ⊗ₜ[K] a) = a := by
  simp [matrixDescentScalarMap]

end Field
