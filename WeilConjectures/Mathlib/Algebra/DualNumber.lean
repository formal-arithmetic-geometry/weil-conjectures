/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.NoncommRing

/-!
# Dual numbers: scaling and matrices

The `R`-algebra endomorphism `ε ↦ cε` of the dual numbers `R[ε]`, and the arithmetic of matrices
over `R[ε]` whose reduction modulo `ε` is the identity: their `ε`-parts add under multiplication.
-/

@[expose] public section

open TrivSqZeroExt

namespace DualNumber

variable {R : Type*} [CommSemiring R]

/-- The `R`-algebra endomorphism `ε ↦ cε` of the dual numbers. -/
def scale (c : R) : R[ε] →ₐ[R] R[ε] :=
  TrivSqZeroExt.map (c • LinearMap.id)

@[simp]
theorem scale_inr (c x : R) : scale c (inr x) = inr (c * x) :=
  TrivSqZeroExt.map_inr _ _

@[simp]
theorem snd_scale (c : R) (x : R[ε]) : (scale c x).snd = c * x.snd :=
  TrivSqZeroExt.snd_map _ _

end DualNumber

namespace Matrix

variable {n : Type*} {R : Type*}

theorem map_inr_mul_map_inr [Fintype n] [Semiring R] (X Y : Matrix n n R) :
    X.map (inr : R → DualNumber R) * Y.map inr = 0 := by
  ext i j : 1
  simp only [Matrix.mul_apply, Matrix.map_apply, inr_mul_inr, Finset.sum_const_zero,
    Matrix.zero_apply]

variable [DecidableEq n] [CommRing R]

/-- A matrix over `R[ε]` reducing to the identity modulo `ε` is `1 + εX`, with `X` its `ε`-part. -/
theorem eq_one_add_map_inr_of_map_fst_eq_one {A : Matrix n n (DualNumber R)}
    (hA : A.map fst = 1) : A = 1 + (A.map snd).map inr := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simpa [Matrix.one_apply, apply_ite fst] using congr_fun₂ hA i j
  · simp [Matrix.one_apply, apply_ite snd]

variable [Fintype n] in
/-- For matrices over `R[ε]` reducing to the identity modulo `ε`, the `ε`-part of a product is
the sum of the `ε`-parts. -/
theorem map_snd_mul_of_map_fst_eq_one {A B : Matrix n n (DualNumber R)}
    (hA : A.map fst = 1) (hB : B.map fst = 1) :
    (A * B).map snd = A.map snd + B.map snd := by
  ext i j
  have hA' (i j) : (A i j).fst = (1 : Matrix n n R) i j := congr_fun₂ hA i j
  have hB' (i j) : (B i j).fst = (1 : Matrix n n R) i j := congr_fun₂ hB i j
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, hA', hB',
    Matrix.one_apply, Finset.sum_add_distrib, add_comm]

variable [Fintype n] in
/-- The mixed term of the commutator of `1 + εX` and `1 + δY` over `R[ε][δ]` is the commutator
`XY - YX`: `(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ(XY - YX)`. -/
theorem map_snd_snd_commutator (X Y : Matrix n n R) :
    ((1 + X.map (fun a ↦ inl (inr a) : R → DualNumber (DualNumber R))) *
        (1 + Y.map fun b ↦ inr (inl b)) * (1 - X.map fun a ↦ inl (inr a)) *
        (1 - Y.map fun b ↦ inr (inl b))).map (fun z ↦ z.snd.snd) = X * Y - Y * X := by
  set P : Matrix n n (DualNumber (DualNumber R)) := X.map fun a ↦ inl (inr a)
  set Q : Matrix n n (DualNumber (DualNumber R)) := Y.map fun b ↦ inr (inl b)
  have hPP : P * P = 0 := by
    ext i j : 1
    simp [P, Matrix.mul_apply, inl_mul_inl, inr_mul_inr, -DualNumber.inr_eq_smul_eps]
  have hQQ : Q * Q = 0 := by
    ext i j : 1
    simp [Q, Matrix.mul_apply, inr_mul_inr, -DualNumber.inr_eq_smul_eps]
  have hPQP : P * Q * P = 0 := by
    ext i j : 1
    simp [P, Q, Matrix.mul_apply, Finset.sum_mul, inl_mul_inr, inr_mul_inl, inr_mul_inr,
      smul_eq_mul, -DualNumber.inr_eq_smul_eps]
  have hQPQ : Q * P * Q = 0 := by
    ext i j : 1
    simp [P, Q, Matrix.mul_apply, Finset.sum_mul, inl_mul_inr, inr_mul_inl, inr_mul_inr,
      smul_eq_mul, -DualNumber.inr_eq_smul_eps]
  have h : (1 + P) * (1 + Q) * (1 - P) * (1 - Q) = 1 + P * Q - Q * P - P * P - Q * Q +
      P * P * Q + Q * P * Q - P * Q * P - P * (Q * Q) + P * Q * P * Q := by
    noncomm_ring
  rw [h, hPP, hQQ, hPQP, hQPQ]
  ext i j
  simp [P, Q, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Matrix.one_apply, apply_ite snd,
    -DualNumber.inr_eq_smul_eps]

end Matrix
