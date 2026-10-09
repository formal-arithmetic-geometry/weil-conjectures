/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Dual numbers: scaling and matrices

The `R`-algebra endomorphism `ε ↦ cε` of the dual numbers `R[ε]`, which is multiplicative in `c`
and reduces to the identity modulo `ε`, the evaluation `R[ε] → R`, `ε ↦ t`, at an element of
square zero, and the arithmetic of matrices over `R[ε]` whose
reduction modulo `ε` is the identity: their `ε`-parts add under multiplication.
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
theorem fst_scale (c : R) (x : R[ε]) : (scale c x).fst = x.fst :=
  TrivSqZeroExt.fst_map _ _

@[simp]
theorem snd_scale (c : R) (x : R[ε]) : (scale c x).snd = c * x.snd :=
  TrivSqZeroExt.snd_map _ _

@[simp]
theorem scale_one : scale (1 : R) = AlgHom.id R R[ε] := by
  ext <;> simp

theorem scale_mul (c d : R) : scale (c * d) = (scale c).comp (scale d) := by
  ext <;> simp

/-- Scaling by zero is the reduction `R[ε] → R` modulo `ε`, followed by the inclusion. -/
theorem scale_zero : scale (0 : R) = (Algebra.ofId R R[ε]).comp (fstHom R R R) := by
  ext <;> simp

@[simp]
theorem fstHom_comp_scale (c : R) : (fstHom R R R).comp (scale c) = fstHom R R R := by
  ext; simp

/-- The evaluation `R[ε] → R`, `a + εb ↦ a + tb`, at an element `t` of square zero. -/
def evalRingHom {R : Type*} [CommRing R] (t : R) (ht : t * t = 0) : R[ε] →+* R where
  toFun x := x.fst + t * x.snd
  map_one' := by simp
  map_mul' x y := by
    simp only [fst_mul, snd_mul]
    linear_combination (-(x.snd * y.snd)) * ht
  map_zero' := by simp
  map_add' x y := by
    simp only [fst_add, snd_add]
    ring

@[simp]
theorem evalRingHom_apply {R : Type*} [CommRing R] (t : R) (ht : t * t = 0) (x : R[ε]) :
    evalRingHom t ht x = x.fst + t * x.snd :=
  rfl

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
