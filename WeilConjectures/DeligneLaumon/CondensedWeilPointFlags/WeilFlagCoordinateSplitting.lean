/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.Matrix.Block
/-! # Split coordinate sequence underlying a Weil flag

The standard coordinate inclusion `Kⁿ → Kⁿ⁺¹` and last-coordinate projection form a split
short exact sequence. This is used in the dimension-zero Jordan filtration step of the proof
that real mixed sheaves are detected by curves.
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures.CondensedWeilPointFlags
/-- The standard inclusion I and projection P, with their coordinate retraction R and
section S, satisfy RI=1, PS=1, PI=0, and IR+SP=1. This includes n=0. -/
theorem coordinate_split_equations {K : Type u} [Field K] (n : ℕ) :
    let I : Matrix (Fin (n+1)) (Fin n) K := fun r k ↦ if r = k.castSucc then 1 else 0
    let R : Matrix (Fin n) (Fin (n+1)) K := I.transpose
    let P : Matrix (Fin 1) (Fin (n+1)) K :=
      fun _ k ↦ if k = Fin.last n then 1 else 0
    let S : Matrix (Fin (n+1)) (Fin 1) K := P.transpose
    R * I = 1 ∧ P * S = 1 ∧ P * I = 0 ∧ I * R + S * P = 1 := by
  classical
  dsimp only
  constructor
  · ext r k
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.castSucc_inj, eq_comm]
  constructor
  · ext r k
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Subsingleton.elim r k]
  constructor
  · ext r k
    simp [Matrix.mul_apply, Fin.castSucc_ne_last]
  · ext r k
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    refine Fin.lastCases ?_ (fun r ↦ ?_) r
    · refine Fin.lastCases ?_ (fun k ↦ ?_) k
      · simp [(fun x : Fin n ↦ (Fin.castSucc_ne_last x).symm)]
      · simp [Fin.castSucc_ne_last,
          (fun x : Fin n ↦ (Fin.castSucc_ne_last x).symm)]
    · refine Fin.lastCases ?_ (fun k ↦ ?_) k
      · simp [Fin.castSucc_ne_last,
          (fun x : Fin n ↦ (Fin.castSucc_ne_last x).symm)]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, Fin.castSucc_inj]
end WeilConjectures.CondensedWeilPointFlags
