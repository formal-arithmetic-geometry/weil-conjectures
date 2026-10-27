/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! # The algebraic last-variable averaging identity

Source: the agent analytic expansion of paragraph (3) of the direct-image stability
proof, steps 3 and 4 of lem-sfb-scalar-cochain-averaging-primitives.
(blueprint: lem-sfb-invariant-average-cochain-identity)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace WeilConjectures

private theorem tail_snoc {G : Type u} {n : ℕ} (g : Fin (n + 1) → G) (h : G) :
    (fun j : Fin (n + 1) ↦ Fin.snoc (α := fun _ ↦ G) g h j.succ) =
      Fin.snoc (α := fun _ ↦ G) (fun j : Fin n ↦ g j.succ) h := by
  ext j
  cases j using Fin.lastCases <;> simp [← Fin.castSucc_succ]

private theorem contract_snoc {G : Type u} [Group G] {n : ℕ}
    (g : Fin (n + 1) → G) (h : G) (j : Fin n) :
    Fin.contractNth j.castSucc.castSucc (· * ·) (Fin.snoc g h) =
      Fin.snoc (Fin.contractNth j.castSucc (· * ·) g) h := by
  ext k
  cases k using Fin.lastCases with
  | last =>
    simp [Fin.contractNth, Nat.not_lt_of_ge (Nat.le_of_lt j.isLt),
      Nat.ne_of_gt j.isLt]
  | cast k =>
    simp only [Fin.contractNth, Fin.val_castSucc, Fin.snoc_castSucc,
      ← Fin.castSucc_succ]

private theorem contract_snoc_penultimate {G : Type u} [Group G] {n : ℕ}
    (g : Fin (n + 1) → G) (h : G) :
    Fin.contractNth (Fin.last n).castSucc (· * ·) (Fin.snoc g h) =
      Fin.snoc (Fin.init g) (g (Fin.last n) * h) := by
  ext k
  cases k using Fin.lastCases with
  | last => simp [Fin.contractNth]
  | cast k => simp [Fin.contractNth, k.isLt, Fin.init]

private theorem contract_last {G : Type u} [Group G] {n : ℕ}
    (g : Fin (n + 1) → G) :
    Fin.contractNth (Fin.last n) (· * ·) g = Fin.init g := by
  ext k
  simp [Fin.contractNth, k.isLt, Fin.init]

/-- A normalized invariant linear average contracts trivial-action cocycles, wherever
all last-variable slices belong to its domain. This assertion is purely algebraic:
there is no continuity, norm, completeness, or finite-quotient assertion.

Source: the agent analytic expansion of paragraph (3) of the direct-image stability
proof, steps 3 and 4 of lem-sfb-scalar-cochain-averaging-primitives.
(blueprint: lem-sfb-invariant-average-cochain-identity)

Proof: Fix a parameter and a tuple of n+1 group elements. Evaluate the cocycle
equation on that tuple with a final variable h appended. Interpret the equation in
E using injectivity of evaluation. The first term is the slice over the tail tuple;
the first n merged faces are slices over the corresponding merged tuples. The next
face is the left translate, by the last group element, of the slice over the initial
tuple. The final face is the constant cocycle value times the unit. Apply the linear
average. Invariance replaces the translated slice by its original; normalization
fixes the constant term. The resulting alternating sum is the differential of the
unsigned average plus (-1)^(n+2) times the original cocycle. Multiplying by
(-1)^(n+1), whose square is one, gives the desired identity. For n=0, the first and
translated slice cancel, so the same equation says the degree-one cocycle is zero;
the two degree-zero faces also cancel. Empty parameter types are vacuous. -/
theorem invariant_average_cochain_identity
    {V : Type v} [Field V] {G : Type u} [Group G] {P : Type w}
    {E : Type z} [AddCommGroup E] [Module V E]
    (ev : E →ₗ[V] (G → V)) (hev : Function.Injective ev)
    (A : E →ₗ[V] V) (oneE : E) (hone : ev oneE = 1) (hAone : A oneE = 1)
    (hleft : ∀ (a : G) (f : E), ∃ f' : E,
      ev f' = (fun h ↦ ev f (a * h)) ∧ A f' = A f)
    (n : ℕ) (c : P × (Fin (n + 1) → G) → V)
    (t : P → (Fin n → G) → E)
    (ht : ∀ s g h, ev (t s g) h = c (s, Fin.snoc g h))
    (hc : ∀ s (g : Fin (n + 2) → G),
      c (s, fun j ↦ g j.succ) +
        ∑ j : Fin (n + 2), (-1 : V) ^ (j.val + 1) *
          c (s, Fin.contractNth j (· * ·) g) = 0) :
    ∀ s (g : Fin (n + 1) → G),
      (-1 : V) ^ (n + 1) * A (t s (fun j ↦ g j.succ)) +
        ∑ j : Fin (n + 1), (-1 : V) ^ (j.val + 1) *
          ((-1 : V) ^ (n + 1) * A (t s (Fin.contractNth j (· * ·) g))) =
        c (s, g) := by
  classical
  intro s g
  obtain ⟨L, hL, hAL⟩ := hleft (g (Fin.last n)) (t s (Fin.init g))
  have hE : t s (fun j ↦ g j.succ) +
      (∑ j : Fin n, (-1 : V) ^ (j.val + 1) •
        t s (Fin.contractNth j.castSucc (· * ·) g)) +
      (-1 : V) ^ (n + 1) • L +
      ((-1 : V) ^ (n + 2) * c (s, g)) • oneE = 0 := by
    apply hev
    ext h
    have heq := hc s (Fin.snoc g h)
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at heq
    simp only [Fin.val_castSucc, Fin.val_last, tail_snoc,
      contract_snoc, contract_snoc_penultimate, contract_last, Fin.init_snoc] at heq
    simpa only [map_add, map_sum, map_smul, map_zero, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ht, hL, hone, Pi.one_apply,
      Pi.zero_apply, mul_one, add_assoc, Nat.reduceAdd] using heq
  have hscalar := congrArg A hE
  simp only [map_add, map_sum, map_smul, map_zero, smul_eq_mul, hAL,
    hAone, mul_one] at hscalar
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, contract_last]
  have hsign : (-1 : V) ^ (n + 1) * (-1 : V) ^ (n + 1) = 1 := by
    rw [← mul_pow]
    simp
  have hnext : (-1 : V) ^ (n + 2) = -((-1 : V) ^ (n + 1)) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ]
    ring
  rw [hnext] at hscalar
  have hscaled := congrArg (fun x : V ↦ (-1 : V) ^ (n + 1) * x) hscalar
  simp only [mul_add, Finset.mul_sum] at hscaled
  have hsum : (∑ j : Fin n, (-1 : V) ^ (n + 1) *
        ((-1 : V) ^ (j.val + 1) * A (t s (Fin.contractNth j.castSucc (· * ·) g)))) =
      ∑ j : Fin n, (-1 : V) ^ (j.val + 1) *
        ((-1 : V) ^ (n + 1) * A (t s (Fin.contractNth j.castSucc (· * ·) g))) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum] at hscaled
  have hlast : (-1 : V) ^ (n + 1) *
      (-((-1 : V) ^ (n + 1)) * c (s, g)) = -c (s, g) := by
    rw [neg_mul, mul_neg, ← mul_assoc, hsign, one_mul]
  rw [hlast, mul_zero] at hscaled
  have hlast' : (-1 : V) ^ (n + 1) *
      ((-1 : V) ^ (n + 1) * A (t s (Fin.init g))) = A (t s (Fin.init g)) := by
    rw [← mul_assoc, hsign, one_mul]
  rw [hlast'] at hscaled ⊢
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg, add_assoc] using hscaled)

end WeilConjectures
