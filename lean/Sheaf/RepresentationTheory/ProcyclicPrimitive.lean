/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E6
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.LocallyConstant.Algebra
import Sheaf.Topology.ContinuousOpenNormalStabilizer
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Algebra.BigOperators.Intervals

/-!
# A locally constant primitive on the l-adic integers

Source: blueprint lem-exc-procyclic-two-term, third proof paragraph.
-/

@[expose] public section

universe w

open scoped BigOperators
open CategoryTheory Topology

namespace Rep

private theorem reduction_locallyConstant (l : ℕ) [Fact l.Prime] (r : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := l) r) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  let ε : ℝ := (l : ℝ) ^ (-(r : ℤ))
  have hε : 0 < ε := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  refine ⟨Metric.ball x ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  intro y hy
  apply sub_eq_zero.mp
  rw [← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
  apply (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mp
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)

private theorem periodic_sum
    {M : Type w} [AddCommGroup M] (f : ℕ → M) (L : ℕ)
    (hf : ∀ n, f (n + L) = f n) (k : ℕ) :
    (∑ n ∈ Finset.range (L * k), f n) = k • ∑ n ∈ Finset.range L, f n := by
  have hshift (n t : ℕ) : f (n + L * t) = f n := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hf, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [Nat.add_comm] using hshift n k

private theorem cyclic_primitive
    {M : Type w} [AddCommGroup M] (N : ℕ) [NeZero N] (f : ℕ → M)
    (hz : (∑ n ∈ Finset.range N, f n) = 0) (a : ZMod N) :
    (∑ n ∈ Finset.range (a + 1).val, f n) -
      (∑ n ∈ Finset.range a.val, f n) = f a.val := by
  have hval : (a + 1).val = (a.val + 1) % N := by
    rw [← Nat.cast_one, ← ZMod.natCast_zmod_val a, ← Nat.cast_add, ZMod.val_natCast]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt a)]
  by_cases h : a.val + 1 < N
  · rw [hval, Nat.mod_eq_of_lt h, Finset.sum_range_succ, add_sub_cancel_left]
  · have heq : a.val + 1 = N := by have := ZMod.val_lt a; omega
    rw [hval, heq, Nat.mod_self, Finset.sum_range_zero, zero_sub]
    have hs : (∑ n ∈ Finset.range a.val, f n) + f a.val = 0 := by
      rw [← Finset.sum_range_succ, heq, hz]
    exact neg_eq_iff_add_eq_zero.mpr hs

set_option linter.style.haveILetI false in
/-- Every locally constant function to an l-power torsion group has a locally constant
primitive for translation by one.

Proof: choose an open subgroup fixing the function under translation. A sufficiently small
power of l lies in this subgroup. The function therefore has period L = l^r on integers.
On N = L*l^s residues its sum is l^s times a sum, hence zero. Its partial sums on the
standard representatives of Z/NZ satisfy the difference equation, including at N-1 because
the total sum is zero. Pull these partial sums back along reduction. The kernel of reduction
is contained in the chosen open subgroup, so the right side is the original function.

Source: blueprint lem-exc-procyclic-two-term, third proof paragraph
(blueprint: lem-exc-procyclic-locally-constant-primitive). -/
theorem exists_procyclic_primitive
    (l : ℕ) [Fact l.Prime] (s : ℕ) (M : Type w) [AddCommGroup M]
    (hM : ∀ m : M, (l ^ s) • m = 0) (f : LocallyConstant ℤ_[l] M) :
    ∃ h : LocallyConstant ℤ_[l] M, ∀ x : ℤ_[l], h (x + 1) - h x = f x := by
  classical
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  let G := Multiplicative ℤ_[l]
  obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
    (ProfiniteGrp.of G) M (fun x ↦ f (Multiplicative.toAdd x)) f.continuous
  have hUopen : IsOpen {x : ℤ_[l] | Multiplicative.ofAdd x ∈ U} := U.isOpen
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 0 U.one_mem
  obtain ⟨r, hr⟩ := PadicInt.exists_pow_neg_lt l hε
  have hmem {x : ℤ_[l]} (hx : ‖x‖ ≤ (l : ℝ) ^ (-(r : ℤ))) :
      Multiplicative.ofAdd x ∈ U := by
    have hxin : x ∈ Metric.ball (0 : ℤ_[l]) ε := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hx.trans_lt hr
    exact hball hxin
  have hper (n : ℕ) : f ((n + l ^ r : ℕ) : ℤ_[l]) = f (n : ℤ_[l]) := by
    have hp : Multiplicative.ofAdd ((l ^ r : ℕ) : ℤ_[l]) ∈ U := by
      apply hmem
      simp only [Nat.cast_pow, PadicInt.norm_p_pow]
      exact le_rfl
    have ht := hU (Multiplicative.ofAdd (n : ℤ_[l])) _ hp
    change f ((n : ℤ_[l]) + ((l ^ r : ℕ) : ℤ_[l])) = f (n : ℤ_[l]) at ht
    simpa only [Nat.cast_add] using ht
  let N := l ^ (r + s)
  letI : NeZero N := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let q := PadicInt.toZModPow (p := l) (r + s)
  have hfactor (x : ℤ_[l]) : f ((q x).val : ℤ_[l]) = f x := by
    have hx : q (x - ((q x).val : ℤ_[l])) = 0 := by simp [q]
    have hn : ‖x - ((q x).val : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r + s : ℤ)) := by
      apply (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
      exact hx
    have hb : (l : ℝ) ^ (-(r + s : ℤ)) ≤ (l : ℝ) ^ (-(r : ℤ)) := by
      apply zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_le)
      omega
    have ht := hU (Multiplicative.ofAdd ((q x).val : ℤ_[l]))
      (Multiplicative.ofAdd (x - ((q x).val : ℤ_[l]))) (hmem (hn.trans hb))
    change f (((q x).val : ℤ_[l]) + (x - ((q x).val : ℤ_[l]))) =
      f ((q x).val : ℤ_[l]) at ht
    simpa only [add_sub_cancel] using ht.symm
  have hsum : (∑ n ∈ Finset.range N, f (n : ℤ_[l])) = 0 := by
    change (∑ n ∈ Finset.range (l ^ (r + s)), f (n : ℤ_[l])) = 0
    rw [pow_add, periodic_sum (fun n ↦ f (n : ℤ_[l])) (l ^ r) hper, hM]
  let h : LocallyConstant ℤ_[l] M :=
    ⟨fun x ↦ ∑ n ∈ Finset.range (q x).val, f (n : ℤ_[l]),
      (reduction_locallyConstant l (r + s)).comp
        (fun a ↦ ∑ n ∈ Finset.range a.val, f (n : ℤ_[l]))⟩
  refine ⟨h, fun x ↦ ?_⟩
  change (∑ n ∈ Finset.range (q (x + 1)).val, f (n : ℤ_[l])) -
    (∑ n ∈ Finset.range (q x).val, f (n : ℤ_[l])) = f x
  rw [map_add, map_one, cyclic_primitive N _ hsum, hfactor]

end Rep
