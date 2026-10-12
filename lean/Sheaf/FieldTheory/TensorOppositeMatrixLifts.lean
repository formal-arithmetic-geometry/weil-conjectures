/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker S2
-/
module

public import Sheaf.FieldTheory.BrauerScalarDefect
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Explicit tensor lifts for an opposite factor

Source: Stacks Project, Tag 03R7, tensor computation.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct Kronecker

/-- Inverse transpose on invertible matrices, constructed using the unit inverse. -/
def matrixInverseTranspose {R : Type*} [CommRing R] {n : Type*}
    [Fintype n] [DecidableEq n] :
    Matrix.GeneralLinearGroup n R →* Matrix.GeneralLinearGroup n R where
  toFun a :=
    { val := (a⁻¹).val.transpose
      inv := a.val.transpose
      val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one] }
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp [Matrix.transpose_mul])

/-- Kronecker product with the inverse transpose of the second factor, reindexed. -/
def tensorOppositeMatrixLift {R : Type*} [CommRing R] {n m : ℕ}
    (a : Matrix.GeneralLinearGroup (Fin n) R)
    (b : Matrix.GeneralLinearGroup (Fin m) R) :
    Matrix.GeneralLinearGroup (Fin (n * m)) R :=
  Units.map (Matrix.reindexRingEquiv R finProdFinEquiv).toMonoidHom
    (a.kronecker (matrixInverseTranspose b))

/-- The matrix lift respects coefficient maps, multiplication, and scalar matrices.

These are the elementary matrix identities used in the tensor-lift construction.
Source: Mathlib matrix Kronecker and reindexing identities.
(blueprint: lem-sc-tensor-opposite-matrix-properties). -/
theorem tensorOppositeMatrixLift_properties {R S : Type*} [CommRing R] [CommRing S]
    {n m : ℕ} (f : R →+* S)
    (a a' : Matrix.GeneralLinearGroup (Fin n) R)
    (b b' : Matrix.GeneralLinearGroup (Fin m) R) (c d : Rˣ) :
    tensorOppositeMatrixLift (Matrix.GeneralLinearGroup.map f a)
        (Matrix.GeneralLinearGroup.map f b) =
      Matrix.GeneralLinearGroup.map f (tensorOppositeMatrixLift a b) ∧
    tensorOppositeMatrixLift (a * a') (b * b') =
      tensorOppositeMatrixLift a b * tensorOppositeMatrixLift a' b' ∧
    tensorOppositeMatrixLift (Matrix.GeneralLinearGroup.scalar (Fin n) c)
        (Matrix.GeneralLinearGroup.scalar (Fin m) d) =
      Matrix.GeneralLinearGroup.scalar (Fin (n * m)) (c / d) := by sorry

/-- The tensor/opposite splitting has the conjugation datum of the explicit tensor lifts.

Proof: commute scalar extension with the tensor product and with opposite algebras.
Apply the two given matrix splittings, transpose the opposite of the second matrix
algebra, and apply the Kronecker algebra equivalence. Reindex the product of the two
finite index sets using finProdFinEquiv. On a pure tensor the coefficient action on
its image is the Kronecker product of the coefficient actions on its two factors.
Use the two conjugation hypotheses. Transposition reverses the second conjugation,
so that its conjugator is the inverse transpose of the second lift. The Kronecker
multiplication formula gives precisely conjugation by tensorOppositeMatrixLift.
Extend from pure tensors by additivity and scalar linearity; coefficient automorphisms
fix the base field, so this extension respects the tensor relations.
Source: Stacks Project, Tag 03R7, tensor computation in the injectivity argument.
(blueprint: lem-sc-tensor-opposite-matrix-conjugation). -/
theorem exists_tensor_opposite_matrix_conjugation (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (n m : ℕ)
    (eA : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (eB : (SeparableClosure K ⊗[K] B) ≃ₐ[SeparableClosure K]
      Matrix (Fin m) (Fin m) (SeparableClosure K))
    (a : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin m) (SeparableClosure K))
    (ha : ∀ (g : Gal(SeparableClosure K/K)) (v : A), (eA (1 ⊗ₜ[K] v)).map g =
      ((a g)⁻¹).val * eA (1 ⊗ₜ[K] v) * (a g).val)
    (hb : ∀ (g : Gal(SeparableClosure K/K)) (v : B), (eB (1 ⊗ₜ[K] v)).map g =
      ((b g)⁻¹).val * eB (1 ⊗ₜ[K] v) * (b g).val) :
    ∃ e : (SeparableClosure K ⊗[K] (A ⊗[K] Bᵐᵒᵖ)) ≃ₐ[SeparableClosure K]
        Matrix (Fin (n * m)) (Fin (n * m)) (SeparableClosure K),
      ∀ (g : Gal(SeparableClosure K/K)) (v : A ⊗[K] Bᵐᵒᵖ),
        (e (1 ⊗ₜ[K] v)).map g =
        ((tensorOppositeMatrixLift (a g) (b g))⁻¹).val *
          e (1 ⊗ₜ[K] v) * (tensorOppositeMatrixLift (a g) (b g)).val := by sorry

end Field
