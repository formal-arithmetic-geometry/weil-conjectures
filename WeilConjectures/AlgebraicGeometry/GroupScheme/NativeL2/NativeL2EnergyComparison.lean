/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Norm
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Comparing the growth exponents of trace energies

Source: latest blueprint, lem-fd-l2-middle-extension.proof.md, final paragraph
(blueprint: lem-fd-l2-energy-comparison).
The argument works for numerical energy sequences, independently of coefficient objects.
-/

@[expose] public section
set_option autoImplicit false

open Filter Topology
namespace WeilConjectures.NativeL2

private theorem normalized_limsup_eq_zero {q : ℕ} (hq : 1 < (q : ℝ))
    {b : ℕ → ℝ} {C B β : ℝ}
    (hb : ∀ m : ℕ, 1 ≤ m → b m ≤ C * (q : ℝ) ^ ((m : ℝ) * B))
    (hβ : B - 1 < β) :
    limsup (fun m : ℕ ↦ ENNReal.ofReal
      (b m / (q : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop = 0 := by
  have hq0 : 0 < (q : ℝ) := by linarith
  have hr1 : (q : ℝ) ^ (B - (β + 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hlim : Tendsto
      (fun m : ℕ ↦ ENNReal.ofReal (C * ((q : ℝ) ^ (B - (β + 1))) ^ m))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr1).const_mul C
    rw [mul_zero] at h
    simpa using ENNReal.tendsto_ofReal h
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_).limsup_eq
  filter_upwards [eventually_ge_atTop 1] with m hm
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by positivity)]
  calc b m ≤ C * (q : ℝ) ^ ((m : ℝ) * B) := hb m hm
    _ = C * ((q : ℝ) ^ (B - (β + 1))) ^ m *
        (q : ℝ) ^ ((m : ℝ) * (β + 1)) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
        ← Real.rpow_add hq0]
      congr 2
      ring

/-- Pointwise domination of energy sequences implies domination of their L² weights.
Source: lem-fd-l2-middle-extension.proof.md, final paragraph, lower bound
(blueprint: lem-fd-l2-energy-comparison). -/
theorem weightOfEnergy_mono (q : ℕ) {a b : ℕ → ℝ} (h : ∀ m, a m ≤ b m) :
    weightOfEnergy q a ≤ weightOfEnergy q b := by
  unfold weightOfEnergy
  refine iSup₂_le fun β hβ ↦ le_iSup₂_of_le β ?_ le_rfl
  exact hβ.trans_le (limsup_le_limsup (Eventually.of_forall fun m ↦
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (h m) (by positivity))))

/-- An exponential error of exponent B contributes at most B-1 to the L² weight.
Source: lem-fd-l2-middle-extension.proof.md, final paragraph, upper bound
(blueprint: lem-fd-l2-energy-comparison). -/
theorem weightOfEnergy_le_max (q : ℕ) (hq : 1 < (q : ℝ)) (a b : ℕ → ℝ)
    {C B : ℝ} (h : ∀ m, b m ≤ a m + C * (q : ℝ) ^ ((m : ℝ) * B)) :
    weightOfEnergy q b ≤ max (weightOfEnergy q a) ((B - 1 : ℝ) : EReal) := by
  unfold weightOfEnergy
  refine iSup₂_le fun β hβ ↦ not_lt.1 fun hlt ↦ hβ.ne' ?_
  rw [max_lt_iff] at hlt
  have hA : limsup (fun m : ℕ ↦ ENNReal.ofReal
      (a m / (q : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop = 0 := by
    by_contra hne
    exact hlt.1.not_ge (le_iSup₂_of_le (f := fun (γ : ℝ)
      (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
        (a m / (q : ℝ) ^ ((m : ℝ) * (γ + 1)))) atTop) ↦ (γ : EReal))
      β (pos_iff_ne_zero.2 hne) le_rfl)
  have hC := normalized_limsup_eq_zero
    (b := fun m : ℕ ↦ C * (q : ℝ) ^ ((m : ℝ) * B)) hq
    (fun _ _ ↦ le_rfl) (EReal.coe_lt_coe_iff.1 hlt.2)
  have ht := (tendsto_of_le_liminf_of_limsup_le zero_le hA.le).add
    (tendsto_of_le_liminf_of_limsup_le zero_le hC.le)
  rw [add_zero] at ht
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ zero_le) fun m ↦
      (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le).limsup_eq
  rw [← add_div]
  exact div_le_div_of_nonneg_right (h m) (by positivity)

/-- An energy sequence of weight w keeps that weight after adding a nonnegative error
bounded by C q^(mw). No restriction on the sign of w, or on C, is required.
Source: lem-fd-l2-middle-extension.proof.md, final paragraph
(blueprint: lem-fd-l2-energy-comparison). -/
theorem weightOfEnergy_eq_of_sandwich (q : ℕ) (hq : 1 < (q : ℝ)) (a b : ℕ → ℝ)
    (w : ℝ) (hw : weightOfEnergy q a = (w : EReal))
    (hle : ∀ m, a m ≤ b m)
    (hbound : ∃ C : ℝ, ∀ m, b m ≤ a m + C * (q : ℝ) ^ ((m : ℝ) * w)) :
    weightOfEnergy q b = weightOfEnergy q a := by
  obtain ⟨C, hC⟩ := hbound
  have hupper := weightOfEnergy_le_max q hq a b hC
  rw [hw, max_eq_left (EReal.coe_le_coe_iff.2 (by linarith))] at hupper
  exact le_antisymm (hupper.trans_eq hw.symm) (weightOfEnergy_mono q hle)

end WeilConjectures.NativeL2
