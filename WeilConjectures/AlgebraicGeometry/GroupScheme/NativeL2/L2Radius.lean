/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Norm
public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius

/-!
# Radius of the squared trace series for condensed Weil pairs

Source: latest blueprint, `lem-wf-l2-radius`, in `sk-lem-wrp-l2-growth`.
The coefficient estimates from the former native-sheaf proof are reused for an arbitrary
nonnegative sequence, then applied to the alternating cohomological trace energy of a
condensed Weil pair. No triangulated structure on the category of pairs is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale Filter Topology
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

section Growth
variable {q : ℝ} {b : ℕ → ℝ}

end Growth

/-- The root-test characterization of exponential growth for a nonnegative sequence.
It holds for radius zero and infinity and is insensitive to the coefficient at index zero.

Proof: positive normalized limsup implies the rescaling is outside the open convergence
disc. Conversely, zero normalized limsup bounds the rescaled coefficients eventually and
puts the rescaling inside the closed convergence radius. Choose an intermediate exponent
using strict monotonicity in the first implication and continuity in the converse.

Source: latest blueprint, `lem-wf-l2-radius`, scalar coefficient argument.
(blueprint: lem-wf-l2-radius-energy) -/
theorem lt_weightOfEnergy_iff {q : ℕ} (hq : 1 < (q : ℝ))
    {b : ℕ → ℝ} (hb : ∀ m, 0 ≤ b m) (β : ℝ) :
    (β : EReal) < weightOfEnergy q b ↔
      (FormalMultilinearSeries.ofScalars ℝ fun n ↦ b (n + 1)).radius <
        ENNReal.ofReal ((q : ℝ) ^ (-(β + 1))) := by
  change (β : EReal) < (⨆ (γ : ℝ) (_ : 0 < limsup (fun m : ℕ ↦
    ENNReal.ofReal (b m / (q : ℝ) ^ ((m : ℝ) * (γ + 1)))) atTop), (γ : EReal)) ↔ _
  have hq0 : 0 < (q : ℝ) := by linarith
  constructor
  · intro h
    obtain ⟨β', h'⟩ := lt_iSup_iff.1 h
    obtain ⟨hpos, hlt⟩ := lt_iSup_iff.1 h'
    refine (radius_le_of_limsup_pos hq hpos).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (by positivity)).2 (Real.rpow_lt_rpow_of_exponent_lt hq ?_))
    linarith [EReal.coe_lt_coe_iff.1 hlt]
  · intro h
    have hc : Tendsto (fun x : ℝ ↦ ENNReal.ofReal ((q : ℝ) ^ (-(x + 1)))) (𝓝[>] β)
        (𝓝 (ENNReal.ofReal ((q : ℝ) ^ (-(β + 1))))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.rpow (by fun_prop)
        fun _ ↦ Or.inl hq0.ne')).tendsto β).mono_left nhdsWithin_le_nhds
    obtain ⟨β', hβ'r, hββ'⟩ := ((hc.eventually (lt_mem_nhds h)).and self_mem_nhdsWithin).exists
    exact (EReal.coe_lt_coe_iff.2 hββ').trans_le (le_iSup₂_of_le β'
      (limsup_pos_of_radius_lt hq hb hβ'r) le_rfl)

end WeilConjectures.NativeL2
