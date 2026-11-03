/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2Series
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Growth of squared Frobenius traces

Source: latest blueprint, part-weights-riemann-hypothesis/sec-purity-real-sheaves/
sec-weights-and-the-growth-of-squared-traces/sk-def-wrp-l2-definition/_section.md,
both defining displays, equivalent description and Complement
(blueprint: sk-def-wrp-l2-definition).

The alternating cohomological trace and its squared energy are the existing condensed
complex constructions of `def-wf-l2-norm`. The logarithm takes values in `EReal`, with
`log 0 = -∞`. Indexing by `n + 1` expresses exactly the positive extension degrees.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale Filter
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

private theorem logarithmicGrowth_eq_weightOfEnergy (q : ℕ) (hq : 1 < (q : ℝ))
    (energy : ℕ → ℝ) :
    limsup (fun n : ℕ ↦ ENNReal.log (ENNReal.ofReal (energy (n + 1))) /
      (Real.log (q : ℝ) : EReal) / ((n + 1 : ℕ) : EReal)) atTop - 1 =
      weightOfEnergy q energy := by
  let b : ℕ → EReal := fun n ↦ ENNReal.log (ENNReal.ofReal (energy (n + 1))) /
    (Real.log (q : ℝ) : EReal) / ((n + 1 : ℕ) : EReal)
  let c := limsup b atTop
  let ratios : ℝ → ℕ → ℝ≥0∞ := fun a n ↦ ENNReal.ofReal
    (energy (n + 1) / (q : ℝ) ^ (((n + 1 : ℕ) : ℝ) * (a + 1)))
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq
  have hb (n : ℕ) (t : ℝ) :
      b n ≤ (t : EReal) ↔ energy (n + 1) ≤ (q : ℝ) ^ (((n + 1 : ℕ) : ℝ) * t) := by
    have hn : (0 : EReal) < ((n + 1 : ℕ) : EReal) := by exact_mod_cast Nat.succ_pos n
    have heq : ENNReal.log (ENNReal.ofReal
        ((q : ℝ) ^ (((n + 1 : ℕ) : ℝ) * t))) =
        (Real.log (q : ℝ) : EReal) * (((n + 1 : ℕ) : EReal) * (t : EReal)) := by
      rw [ENNReal.log_ofReal_of_pos (Real.rpow_pos_of_pos hq0 _), Real.log_rpow hq0]
      rw [← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_mul]
      congr 1
      ring
    dsimp [b]
    rw [EReal.div_le_iff_le_mul hn (EReal.natCast_ne_top _),
      EReal.div_le_iff_le_mul (by exact_mod_cast hlogq) (EReal.coe_ne_top _),
      ← heq, ENNReal.log_le_log_iff, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  have hupper (a : ℝ) (ha : c < ((a + 1 : ℝ) : EReal)) :
      limsup (ratios a) atTop = 0 := by
    obtain ⟨t, hct, hta⟩ := EReal.lt_iff_exists_real_btwn.mp ha
    have hta' : t < a + 1 := by exact_mod_cast hta
    have hev : ∀ᶠ n : ℕ in atTop, b n < (t : EReal) :=
      eventually_lt_of_limsup_lt hct
    have hr : (q : ℝ) ^ (t - (a + 1)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
    have hlim : Tendsto (fun n : ℕ ↦
        ENNReal.ofReal (((q : ℝ) ^ (t - (a + 1))) ^ (n + 1))) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal
          ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).comp
            (tendsto_add_atTop_nat 1))
    refine (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ ↦ zero_le) ?_).limsup_eq
    filter_upwards [hev] with n hn
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (by positivity)]
    calc energy (n + 1) ≤ (q : ℝ) ^ (((n + 1 : ℕ) : ℝ) * t) := (hb n t).mp hn.le
      _ = ((q : ℝ) ^ (t - (a + 1))) ^ (n + 1) *
          (q : ℝ) ^ (((n + 1 : ℕ) : ℝ) * (a + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
        congr 1
        ring
  have hlower (a : ℝ) (ha : ((a + 1 : ℝ) : EReal) < c) :
      0 < limsup (ratios a) atTop := by
    obtain ⟨t, hat, htc⟩ := EReal.lt_iff_exists_real_btwn.mp ha
    have hat' : a + 1 < t := by exact_mod_cast hat
    have hfreq : ∃ᶠ n : ℕ in atTop, (t : EReal) < b n :=
      frequently_lt_of_lt_limsup (h := htc)
    have hfreq' : ∃ᶠ n : ℕ in atTop, 1 ≤ ratios a n := by
      apply hfreq.mono
      intro n hn
      have ht : (q : ℝ) ^ (((n + 1 : ℕ) : ℝ) * t) < energy (n + 1) :=
        lt_of_not_ge (fun h ↦ hn.not_ge ((hb n t).mpr h))
      dsimp [ratios]
      rw [ENNReal.one_le_ofReal, le_div_iff₀ (by positivity), one_mul]
      apply le_trans _ ht.le
      exact Real.rpow_le_rpow_of_exponent_le hq.le
        (mul_le_mul_of_nonneg_left hat'.le (by positivity))
    exact zero_lt_one.trans_le (le_limsup_of_frequently_le hfreq')
  have hweight : weightOfEnergy q energy =
      ⨆ (a : ℝ) (_ : 0 < limsup (ratios a) atTop), (a : EReal) := by
    unfold weightOfEnergy
    apply iSup_congr
    intro a
    have heq : limsup (ratios a) atTop = limsup (fun m : ℕ ↦ ENNReal.ofReal
        (energy m / (q : ℝ) ^ ((m : ℝ) * (a + 1)))) atTop :=
      limsup_nat_add (fun m : ℕ ↦ ENNReal.ofReal
        (energy m / (q : ℝ) ^ ((m : ℝ) * (a + 1)))) 1
    rw [heq]
  change c - 1 = weightOfEnergy q energy
  rw [hweight]
  apply le_antisymm
  · apply le_of_forall_lt
    intro x hx
    obtain ⟨a, hxa, hac⟩ := EReal.lt_iff_exists_real_btwn.mp hx
    have hac' : ((a + 1 : ℝ) : EReal) < c := by
      simpa using EReal.add_lt_of_lt_sub hac
    apply hxa.trans_le
    exact le_iSup_of_le a (le_iSup (fun _ : 0 < limsup (ratios a) atTop ↦
      (a : EReal)) (hlower a hac'))
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    by_contra h
    have hca : c < ((a + 1 : ℝ) : EReal) := by
      have h' : c - 1 < (a : EReal) := lt_of_not_ge h
      simpa using (EReal.sub_lt_iff (.inl (EReal.coe_ne_bot 1)) (.inl (EReal.coe_ne_top 1))).mp h'
    exact ha.ne' (hupper a hca)

/-- The logarithmic growth parameter of the actual condensed Weil complex.
`ENNReal.log` sends zero energy to `-∞`; dividing by `log q` gives the base-q logarithm.
The second divisor is the positive integer `n + 1`, and the final subtraction is the
curve's dimension one. No boundedness or finiteness assumption on growth is imposed.

Source: latest blueprint, defining display for ν(K)
(blueprint: sk-def-wrp-l2-definition). -/
def growthParameter (_hl : l ≠ D.p)
    [IsAffine X₀.left] [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) : EReal :=
  limsup (fun n : ℕ ↦
    ENNReal.log (ENNReal.ofReal (complexTraceEnergy D l X₀ ι K (n + 1))) /
      (Real.log (D.q : ℝ) : EReal) / ((n + 1 : ℕ) : EReal)) atTop - 1

/-- The logarithmic definition is the detail node's L²-weight parameter, including
both infinite endpoints and the empty admissible parameter set.

Source: latest blueprint, equivalent description and Complement
(blueprint: sk-def-wrp-l2-definition).

Proof: use the identical finite alternating stalk traces and energies of def-wf-l2-norm.
Put b_n = log_q(S_n)/n and c = limsup b_n. If a+1 > c, choose c < u < a+1;
eventually S_n ≤ q^(nu), so the normalized energy is bounded by
(q^(u-a-1))^n and tends to zero. If a+1 < c, choose a+1 < v < c;
arbitrarily far out S_n > q^(nv), so the normalized tail suprema are infinite.
Thus all a < c-1 are admissible and no a > c-1 is admissible. Their supremum is c-1,
regardless of endpoint membership. When c = -∞ the admissible set is empty, and when
c = +∞ all real parameters are admissible. Positive reindexing does not change limsup.
This is precisely complexL2Weight's extended-real supremum. -/
theorem growthParameter_eq_complexL2Weight (hl : l ≠ D.p)
    [IsAffine X₀.left] [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) :
    growthParameter D l X₀ hl ι K = complexL2Weight D l X₀ ι K := by
  have hq : 1 < (D.q : ℝ) := by
    rw [← D.card_base]
    exact_mod_cast (Finite.one_lt_card (α := D.k₀))
  exact logarithmicGrowth_eq_weightOfEnergy D.q hq
    (complexTraceEnergy D l X₀ ι K)

/-- The series in the Complement has coefficient S_(n+1) in degree n.

Source: latest blueprint, Complement, citing def-wf-l2-series
(blueprint: sk-def-wrp-l2-definition).

Proof: the existing l2Series is PowerSeries.mk of the energy sequence reindexed by n+1.
Apply PowerSeries.coeff_mk. This is exactly ∑_(m≥1) S_m t^(m-1). -/
theorem growthSeries_coeff (hl : l ≠ D.p)
    [IsAffine X₀.left] [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (n : ℕ) :
    PowerSeries.coeff n (l2Series D l hl X₀ ι K) =
      complexTraceEnergy D l X₀ ι K (n + 1) := by
  exact PowerSeries.coeff_mk _ _

end WeilConjectures.NativeL2
