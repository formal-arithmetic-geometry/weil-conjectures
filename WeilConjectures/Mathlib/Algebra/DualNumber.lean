/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.Matrix.Mul

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

end Matrix
