/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Growth
public import WeilConjectures.AlgebraicGeometry.GroupScheme.RealLinearWeights.RealLinearWeights
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

import Mathlib.Analysis.Asymptotics.ExpGrowth
import Mathlib.Analysis.Analytic.RadiusLiminf

/-! # Growth and finite corrections for squared Frobenius traces

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-purity-real-sheaves/sec-weights-and-the-growth-of-squared-traces/
sk-lem-wrp-l2-growth/_section.md and sk-lem-wrp-l2-growth.proof.md, statement and
its three-paragraph proof (blueprint: sk-lem-wrp-l2-growth).

All energies and growth parameters are the recorded condensed-complex constructions.
Closed-point sums include the degree multiplicity, so they are exactly rational-point sums.
The constant twist below uses the right unit constraint to express tensoring with B_b
on the same underlying derived object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2
open NativeCondensedModule Filter Function
open scoped ENNReal NNReal

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsAffine X₀.left] [IsSeparated X₀.hom] [SmoothOfRelativeDimension 1 X₀.hom]
  [GeometricallyConnected X₀.hom]

private theorem log_growth_rescale (u : ℕ → ℝ≥0∞) (b : ℝ) (hb : 0 < b) :
    limsup (fun n : ℕ ↦ ENNReal.log (u (n + 1)) / (b : EReal) /
      ((n + 1 : ℕ) : EReal)) atTop = ExpGrowth.expGrowthSup u / (b : EReal) := by
  have h : (fun n : ℕ ↦ ENNReal.log (u (n + 1)) / (b : EReal) /
      ((n + 1 : ℕ) : EReal)) =
      (fun n : ℕ ↦ (b : EReal)⁻¹ *
        (ENNReal.log (u (n + 1)) / ((n + 1 : ℕ) : EReal))) := by
    funext n
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [h, EReal.limsup_const_mul_of_nonneg_of_ne_top
    (by simpa only [← EReal.coe_inv, EReal.coe_nonneg] using (inv_pos.mpr hb).le)
    (by rw [← EReal.coe_inv]; exact EReal.coe_ne_top _)]
  rw [Filter.limsup_nat_add (fun n : ℕ ↦ ENNReal.log (u n) / (n : EReal)) 1]
  simp only [ExpGrowth.expGrowthSup, div_eq_mul_inv, mul_comm]

private theorem normalized_max (A B : EReal) (a b : ℝ) (hb : 0 < b)
    (hAB : A ≤ max B ((a * b : ℝ) : EReal)) :
    A / (b : EReal) - 1 ≤ max (B / (b : EReal) - 1) ((a - 1 : ℝ) : EReal) := by
  have hf : Monotone (fun x : EReal ↦ x / (b : EReal) - 1) := by
    intro x y hxy
    exact EReal.sub_le_sub (EReal.div_le_div_right_of_nonneg (c := (b : EReal))
      (by exact_mod_cast hb.le) hxy) le_rfl
  have hh := hf hAB
  dsimp only at hh
  rw [hf.map_max] at hh
  have hc : ((a * b : ℝ) : EReal) / (b : EReal) - 1 = ((a - 1 : ℝ) : EReal) := by
    rw [← EReal.coe_div, mul_div_cancel_right₀ a hb.ne',
      ← EReal.coe_one, ← EReal.coe_sub]
  simpa only [hc] using hh


private theorem q_log_pos : 0 < Real.log (D.q : ℝ) := by
  apply Real.log_pos
  have hq : 1 < D.q := by
    rw [D.cardinality_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt (Nat.zero_lt_one.trans_le D.exponent_pos))
      D.prime.one_lt
  exact_mod_cast hq

omit [IsAffine X₀.left] [IsSeparated X₀.hom]
  [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom] in
private theorem closed_trace_support (n : ℕ) (hn : 1 ≤ n)
    (f : {x : X₀.left // x ∈ closedPoints X₀.left} → ℝ) :
    HasFiniteSupport (fun x ↦ if NativeCondensedModule.localClosedPointDegree D X₀ x ∣ n then
      (NativeCondensedModule.localClosedPointDegree D X₀ x : ℝ) * f x else 0) := by
  classical
  have hs : {x : {x : X₀.left // x ∈ closedPoints X₀.left} |
      NativeCondensedModule.localClosedPointDegree D X₀ x ≤ n}.Finite := by
    have hfin := X₀.hom.finite_setOf_degreeOver_le n
    let e : {x : X₀.left // x ∈ closedPoints X₀.left} ↪ X₀.left.finitePoints :=
      ⟨fun x ↦ ⟨x.val, by rw [X₀.hom.finitePoints_eq_closedPoints]; exact x.property⟩,
        fun x y hxy ↦ Subtype.ext (congrArg (fun z : X₀.left.finitePoints ↦ z.val) hxy)⟩
    exact hfin.preimage (f := e) e.injective.injOn
  apply hs.subset
  intro x hx
  simp only [Function.mem_support] at hx
  split_ifs at hx with h
  · exact Nat.le_of_dvd (by omega) h
  · exact (hx rfl).elim

omit [IsAffine X₀.left] [IsSeparated X₀.hom]
  [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom] in
private theorem energy_nonneg (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (n : ℕ) :
    0 ≤ complexTraceEnergy D l X₀ ι K n := by
  unfold complexTraceEnergy
  split_ifs
  · exact le_rfl
  · apply finsum_nonneg
    intro x
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    · exact le_rfl

private theorem growth_as_expGrowth (hl : l ≠ D.p) (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) :
    growthParameter D l X₀ hl ι K =
      ExpGrowth.expGrowthSup (fun n ↦ ENNReal.ofReal
        (complexTraceEnergy D l X₀ ι K n)) / (Real.log (D.q : ℝ) : EReal) - 1 := by
  unfold growthParameter
  rw [log_growth_rescale (fun n ↦
    ENNReal.ofReal (complexTraceEnergy D l X₀ ι K n)) _ (q_log_pos D)]

private theorem square_norm_le (z w : ℂ) :
    ‖z‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 + 2 * ‖z - w‖ ^ 2 := by
  have h := norm_le_norm_add_norm_sub' z w
  nlinarith [sq_nonneg (‖w‖ - ‖z - w‖), norm_nonneg z,
    norm_nonneg w, norm_nonneg (z - w)]

omit [IsAffine X₀.left] [IsSeparated X₀.hom]
  [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom] in
private theorem energy_triangle (ι : PadicAlgCl l →+* ℂ)
    (K L : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (n : ℕ) (hn : 1 ≤ n) :
    complexTraceEnergy D l X₀ ι K n ≤ 2 * complexTraceEnergy D l X₀ ι L n +
      2 * (∑ᶠ x : {x : X₀.left // x ∈ closedPoints X₀.left},
        if NativeCondensedModule.localClosedPointDegree D X₀ x ∣ n then
          (NativeCondensedModule.localClosedPointDegree D X₀ x : ℝ) *
            ‖ι (complexClosedPowerTrace D l X₀ K x
                (n / NativeCondensedModule.localClosedPointDegree D X₀ x) -
              complexClosedPowerTrace D l X₀ L x
                (n / NativeCondensedModule.localClosedPointDegree D X₀ x))‖ ^ 2
        else 0) := by
  classical
  let f := fun x ↦ if NativeCondensedModule.localClosedPointDegree D X₀ x ∣ n then
    (NativeCondensedModule.localClosedPointDegree D X₀ x : ℝ) *
      ‖ι (complexClosedPowerTrace D l X₀ K x
        (n / NativeCondensedModule.localClosedPointDegree D X₀ x))‖ ^ 2 else 0
  let g := fun x ↦ if NativeCondensedModule.localClosedPointDegree D X₀ x ∣ n then
    (NativeCondensedModule.localClosedPointDegree D X₀ x : ℝ) *
      ‖ι (complexClosedPowerTrace D l X₀ L x
        (n / NativeCondensedModule.localClosedPointDegree D X₀ x))‖ ^ 2 else 0
  let e := fun x ↦ if NativeCondensedModule.localClosedPointDegree D X₀ x ∣ n then
    (NativeCondensedModule.localClosedPointDegree D X₀ x : ℝ) *
      ‖ι (complexClosedPowerTrace D l X₀ K x
          (n / NativeCondensedModule.localClosedPointDegree D X₀ x) -
        complexClosedPowerTrace D l X₀ L x
          (n / NativeCondensedModule.localClosedPointDegree D X₀ x))‖ ^ 2 else 0
  have hf : HasFiniteSupport f := closed_trace_support D X₀ n hn _
  have hg : HasFiniteSupport g := closed_trace_support D X₀ n hn _
  have he : HasFiniteSupport e := closed_trace_support D X₀ n hn _
  have hfg : f ≤ fun x ↦ 2 * g x + 2 * e x := by
    intro x
    dsimp [f, g, e]
    split_ifs
    · have h := mul_le_mul_of_nonneg_left
        (square_norm_le
          (ι (complexClosedPowerTrace D l X₀ K x
            (n / NativeCondensedModule.localClosedPointDegree D X₀ x)))
          (ι (complexClosedPowerTrace D l X₀ L x
            (n / NativeCondensedModule.localClosedPointDegree D X₀ x))))
        (Nat.cast_nonneg (α := ℝ) (NativeCondensedModule.localClosedPointDegree D X₀ x))
      rw [← map_sub] at h
      nlinarith
    · simp
  have hg2 : HasFiniteSupport (fun x ↦ 2 * g x) := HasFiniteSupport.mul_right _ hg
  have he2 : HasFiniteSupport (fun x ↦ 2 * e x) := HasFiniteSupport.mul_right _ he
  have hsum := finsum_le_finsum' hf (hg2.add he2) hfg
  change (∑ᶠ x, f x) ≤ ∑ᶠ x, (2 * g x + 2 * e x) at hsum
  rw [finsum_add_distrib hg2 he2, ← mul_finsum, ← mul_finsum] at hsum
  simpa only [complexTraceEnergy, if_neg (by omega : n ≠ 0)] using hsum

private theorem growth_le_max_of_energy_bound (hl : l ≠ D.p) (ι : PadicAlgCl l →+* ℂ)
    (K L : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (a C : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → complexTraceEnergy D l X₀ ι K n ≤
      2 * complexTraceEnergy D l X₀ ι L n + 2 * C * (D.q : ℝ) ^ ((n : ℝ) * a)) :
    growthParameter D l X₀ hl ι K ≤
      max (growthParameter D l X₀ hl ι L) ((a - 1 : ℝ) : EReal) := by
  let B := 2 * max 1 C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hq : 0 < (D.q : ℝ) := by
    have hq' : 1 < D.q := by
      rw [D.cardinality_eq]
      exact Nat.one_lt_pow (Nat.ne_of_gt (Nat.zero_lt_one.trans_le D.exponent_pos))
        D.prime.one_lt
    exact lt_trans zero_lt_one (by exact_mod_cast hq')
  have hbound : ∀ᶠ n in Filter.atTop,
      ENNReal.ofReal (complexTraceEnergy D l X₀ ι K n) ≤ ENNReal.ofReal B *
        (ENNReal.ofReal (complexTraceEnergy D l X₀ ι L n) +
          EReal.exp (((a * Real.log (D.q : ℝ) : ℝ) : EReal) * n)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hpow : 0 ≤ (D.q : ℝ) ^ ((n : ℝ) * a) := Real.rpow_nonneg hq.le _
    have hreal : complexTraceEnergy D l X₀ ι K n ≤
        B * (complexTraceEnergy D l X₀ ι L n + (D.q : ℝ) ^ ((n : ℝ) * a)) := by
      have hL := energy_nonneg D l X₀ ι L n
      have hm := le_max_right (1 : ℝ) C
      have h1 := le_max_left (1 : ℝ) C
      have hh := h n hn
      dsimp [B]
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hL,
        mul_nonneg (sub_nonneg.mpr hm) hpow]
    have he : ENNReal.ofReal ((D.q : ℝ) ^ ((n : ℝ) * a)) =
        EReal.exp (((a * Real.log (D.q : ℝ) : ℝ) : EReal) * n) := by
      rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_mul, EReal.exp_coe,
        Real.rpow_def_of_pos hq]
      congr 2
      ring
    have he' := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul hB,
      ENNReal.ofReal_add (energy_nonneg D l X₀ ι L n) hpow, he] at he'
    exact he'
  have hg := ExpGrowth.expGrowthSup_le_of_eventually_le ENNReal.ofReal_ne_top hbound
  have hg' : ExpGrowth.expGrowthSup
      (fun n ↦ ENNReal.ofReal (complexTraceEnergy D l X₀ ι K n)) ≤
      max (ExpGrowth.expGrowthSup
        (fun n ↦ ENNReal.ofReal (complexTraceEnergy D l X₀ ι L n)))
        ((a * Real.log (D.q : ℝ) : ℝ) : EReal) := by
    change ExpGrowth.expGrowthSup
        (fun n ↦ ENNReal.ofReal (complexTraceEnergy D l X₀ ι K n)) ≤
      ExpGrowth.expGrowthSup
        ((fun n ↦ ENNReal.ofReal (complexTraceEnergy D l X₀ ι L n)) +
          fun n : ℕ ↦ EReal.exp (((a * Real.log (D.q : ℝ) : ℝ) : EReal) * n)) at hg
    rwa [ExpGrowth.expGrowthSup_add, ExpGrowth.expGrowthSup_exp] at hg
  simpa only [growth_as_expGrowth D l X₀ hl ι] using
    normalized_max _ _ a (Real.log (D.q : ℝ)) (q_log_pos D) hg'

private theorem linear_growth_shift (u : ℕ → EReal) :
    LinearGrowth.linearGrowthSup (fun n ↦ u (n + 1)) =
      LinearGrowth.linearGrowthSup u := by
  apply le_antisymm
  · apply le_of_forall_gt
    intro a ha
    obtain ⟨b, hb, hba⟩ := EReal.exists_between_coe_real ha
    have h := LinearGrowth.eventually_le_mul hb
    have hshift : ∀ᶠ n in atTop, u (n + 1) ≤ (b : EReal) * n + b := by
      filter_upwards [(tendsto_add_atTop_nat 1).eventually h] with n hn
      have heq : (b : EReal) * ((n + 1 : ℕ) : EReal) =
          (b : EReal) * n + b := by
        rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_mul,
          ← EReal.coe_coe_eq_natCast, ← EReal.coe_mul, ← EReal.coe_add]
        congr 1
        push_cast
        ring
      exact hn.trans_eq heq
    exact (LinearGrowth.linearGrowthSup_le_of_eventually_le (EReal.coe_ne_top b)
      hshift).trans_lt (LinearGrowth.linearGrowthSup_const_mul_self.trans_lt hba)
  · apply le_of_forall_gt
    intro a ha
    obtain ⟨b, hb, hba⟩ := EReal.exists_between_coe_real ha
    have h := LinearGrowth.eventually_le_mul hb
    have hshift : ∀ᶠ n in atTop, u n ≤ (b : EReal) * n + (-b : ℝ) := by
      filter_upwards [(tendsto_sub_atTop_nat 1).eventually h, eventually_ge_atTop 1]
        with n hn hn1
      rw [Nat.sub_add_cancel hn1] at hn
      have heq : (b : EReal) * ((n - 1 : ℕ) : EReal) =
          (b : EReal) * n + (-b : ℝ) := by
        rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_mul,
          ← EReal.coe_coe_eq_natCast, ← EReal.coe_mul, ← EReal.coe_add]
        congr 1
        rw [Nat.cast_sub hn1, Nat.cast_one]
        ring
      exact hn.trans_eq heq
    exact (LinearGrowth.linearGrowthSup_le_of_eventually_le (EReal.coe_ne_top (-b))
      hshift).trans_lt (LinearGrowth.linearGrowthSup_const_mul_self.trans_lt hba)

private theorem radius_log (c : ℕ → ℂ) :
    ENNReal.log (FormalMultilinearSeries.ofScalars ℂ c).radius =
      -ExpGrowth.expGrowthSup (fun n ↦ ENNReal.ofReal ‖c n‖) := by
  have h := (FormalMultilinearSeries.ofScalars ℂ c).radius_inv_eq_limsup
  apply_fun ENNReal.log at h
  rw [ENNReal.log_inv] at h
  have hm := ENNReal.log_monotone.map_limsup_of_continuousAt (F := atTop)
    (fun n ↦ ((‖FormalMultilinearSeries.ofScalars ℂ c n‖₊ ^
      (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) ENNReal.continuous_log.continuousAt
  rw [hm] at h
  have hr :
      (fun n ↦ ENNReal.log
        ((‖FormalMultilinearSeries.ofScalars ℂ c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) =
      (fun n ↦ ENNReal.log (ENNReal.ofReal ‖c n‖) / (n : EReal)) := by
    funext n
    rw [ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.log_rpow]
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
      FormalMultilinearSeries.ofScalars_norm]
    simp only [div_eq_mul_inv]
    ac_rfl
  change -ENNReal.log (FormalMultilinearSeries.ofScalars ℂ c).radius =
    limsup (fun n ↦ ENNReal.log
      ((‖FormalMultilinearSeries.ofScalars ℂ c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞))
      atTop at h
  rw [hr] at h
  simpa only [neg_neg, ExpGrowth.expGrowthSup] using congrArg Neg.neg h

/-- Tensor with the specified constant Weil line, using its canonical coefficient basis.
Its underlying complex is unchanged; the structure is followed by multiplication by b.
Multiplication is the actual scalar of ConstantWeil, placed in degree zero and acting
through the derived right unitor. This is the unit-normalized tensor construction,
not an arbitrary endomorphism or a chosen trace realization.
Source: latest blueprint, twist sentence and middle proof paragraph
(blueprint: sk-lem-wrp-l2-growth). -/
def growthTwist
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ) :
    condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom :=
  ⟨CategoryTheory.Endofunctor.IsoAlgebra.mk K.obj.carrier
    (K.obj.str ≪≫ (ρ_ K.obj.carrier).symm ≪≫
      (Iso.refl K.obj.carrier ⊗ᵢ
        (DerivedCategory.singleFunctor _ 0).mapIso
          (CondensedRing.ConstantWeil.scalar l (D.geometricFiber X₀).left b)) ≪≫
      ρ_ K.obj.carrier), K.property⟩

/-- The radius is q^(-nu-1), with infinite radius for nu=-infinity and zero radius
for nu=+infinity. The coefficients are those of the recorded L²-series.
Source: latest blueprint, first sentence and first proof paragraph
(blueprint: sk-lem-wrp-l2-growth).
Proof: put c=limsup log_q(S_n)/n. If |t|<q^(-c), choose u>c with q^u|t|<1.
Eventually S_n<=q^(nu), so the absolute terms are bounded by the summable geometric
sequence q^u(q^u|t|)^(n-1). If |t|>q^(-c), choose v<c with q^v|t|>1.
Infinitely many S_n>=q^(nv); the terms then do not tend to zero. These arguments
also give infinite radius when c=-infinity and zero radius when c=+infinity.
Since nu=c-1, the formula follows. EReal.exp implements both endpoint conventions. -/
theorem growth_radius (hl : l ≠ D.p) (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) :
    (FormalMultilinearSeries.ofScalars ℂ
      (fun n ↦ ((PowerSeries.coeff n (l2Series D l hl X₀ ι K) : ℝ) : ℂ))).radius =
      EReal.exp (-(growthParameter D l X₀ hl ι K + 1) * (Real.log (D.q : ℝ) : EReal)) := by
  let c : ℕ → ℂ := fun n ↦
    ((PowerSeries.coeff n (l2Series D l hl X₀ ι K) : ℝ) : ℂ)
  have hc (n : ℕ) : ‖c n‖ = complexTraceEnergy D l X₀ ι K (n + 1) := by
    simp only [c, l2Series, PowerSeries.coeff_mk, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (energy_nonneg D l X₀ ι K (n + 1))]
  have hg : ExpGrowth.expGrowthSup (fun n ↦ ENNReal.ofReal ‖c n‖) =
      ExpGrowth.expGrowthSup
        (fun n ↦ ENNReal.ofReal (complexTraceEnergy D l X₀ ι K n)) := by
    simp_rw [hc]
    exact linear_growth_shift
      (fun n ↦ ENNReal.log (ENNReal.ofReal (complexTraceEnergy D l X₀ ι K n)))
  have hν : growthParameter D l X₀ hl ι K + 1 =
      ExpGrowth.expGrowthSup
        (fun n ↦ ENNReal.ofReal (complexTraceEnergy D l X₀ ι K n)) /
          (Real.log (D.q : ℝ) : EReal) := by
    rw [growth_as_expGrowth]
    exact EReal.sub_add_cancel (b := 1)
  change (FormalMultilinearSeries.ofScalars ℂ c).radius = _
  rw [← ENNReal.exp_log (FormalMultilinearSeries.ofScalars ℂ c).radius,
    radius_log, hg, hν, EReal.neg_mul]
  rw [EReal.div_mul_cancel (by simp) (by simp)
    (by simpa using (q_log_pos D).ne')]


/-- A punctual eigenvalue upper bound bounds the L² growth of a lisse sheaf.
Source: latest blueprint, second sentence and middle proof paragraph
(blueprint: sk-lem-wrp-l2-growth).
Proof: at a point rational over k_n of degree d dividing n, Frobenius is conjugate
to F_x^(n/d). For rank r the triangle inequality bounds the trace by r*q^(na/2).
The affine curve has at most D*q^n rational points, giving energy at most
D*r^2*q^(n(a+1)). For every beta>a, normalization by q^(n(beta+1)) tends to zero
geometrically. The supremum characterization of nu therefore gives nu<=a.
Zero rank and empty rational-point sets give zero contributions. -/
theorem lisse_growth_le (hl : l ≠ D.p) (ι : PadicAlgCl l →+* ℂ)
    (M : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.obj.carrier)
    (a : ℝ) (hM : HasPunctualWeightsAtMost D l X₀ M.obj ι a) :
    l2Weight D l X₀ ι M.obj ≤ (a : EReal) := by
  sorry

/-- A finitely supported complex with a common stalk eigenvalue bound has
S_n<=C*q^(na) and nu<=a-1, without a cohomological-degree shift in that bound.
Source: latest blueprint, third sentence and middle proof paragraph
(blueprint: sk-lem-wrp-l2-growth).
Proof: the finite closed support has a uniformly bounded number N of geometric
points. Bounded constructibility gives a uniform bound R on the sum of stalk ranks
over all cohomological degrees. Local Frobenius powers and the triangle inequality
bound every alternating stalk trace by R*q^(na/2). Thus S_n<=N*R^2*q^(na).
For beta>a-1, normalization is bounded by C*q^(-n(beta+1-a)), which tends to zero.
The supremum characterization gives nu<=a-1, including the empty support case. -/
theorem finite_support_growth_le (hl : l ≠ D.p) (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (Z : Finset {x : X₀.left // x ∈ closedPoints X₀.left})
    (hZ : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left}), x ∉ Z →
      ∀ (j : ℤ) (i : X₀.left.residueField x.val →+* D.k)
        (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
        IsZero (fibre l D (complexCohomology D l X₀ K j).carrier
          (localClosedPoint D X₀ x i hi)))
    (a : ℝ)
    (hK : ∀ (j : ℤ) (x : {x : X₀.left // x ∈ closedPoints X₀.left})
      (i : X₀.left.residueField x.val →+* D.k)
      (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (α : ULift.{u + 1} (PadicAlgCl l)),
      Module.End.HasEigenvalue (closedOperator D l X₀
        (complexCohomology D l X₀ K j) x i hi).hom α →
        ‖ι α.down‖ ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (a / 2)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      complexTraceEnergy D l X₀ ι K n ≤ C * (D.q : ℝ) ^ ((n : ℝ) * a)) ∧
    growthParameter D l X₀ hl ι K ≤ ((a - 1 : ℝ) : EReal) := by
  sorry

/-- Constant Weil twisting shifts nu by lambda_iota(b)=2*log_q|iota(b)|.
Source: latest blueprint, twist sentence and middle proof paragraph
(blueprint: sk-lem-wrp-l2-growth).
Proof: the unit-normalized tensor with B_b multiplies the degree-n Frobenius
on each cohomological stalk by b^n. Its alternating trace is multiplied by b^n,
so its energy is |iota(b)|^(2n)*S_n=q^(n*lambda_iota(b))*S_n.
The logarithmic quotient is consequently translated by lambda_iota(b), also at
zero energies where both logarithms are -infinity. Translation commutes with
extended-real limsup, including both infinite growth endpoints. -/
theorem growth_twist (hl : l ≠ D.p) (ι : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ) :
    growthParameter D l X₀ hl ι (growthTwist D l X₀ K b) =
      growthParameter D l X₀ hl ι K +
        (WeilGroup.frobeniusWeight ι D.q (b : PadicAlgCl l) : EReal) := by
  sorry

/-- Finite trace corrections below the larger growth exponent preserve that exponent.
The correction is a difference of trace functions; no realization by a complex is assumed.
Source: latest blueprint, final display and final proof paragraph
(blueprint: sk-lem-wrp-l2-growth).
Proof: |z+u|^2<=2|z|^2+2|u|^2 gives S_n(K)<=2*S_n(L)+2*C*q^(na)
and its symmetric counterpart. Normalize by q^(n(beta+1)) for
beta>max(nu(L),a-1). Both terms tend to zero, giving
nu(K)<=max(nu(L),a-1); interchange K and L for the other inequality.
If either exponent is larger than a-1 these inequalities force equality,
also when that exponent is +infinity. The difference need not be a complex trace. -/
theorem growth_eq_of_finite_correction (hl : l ≠ D.p) (ι : PadicAlgCl l →+* ℂ)
    (K L : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (Z : Finset {x : X₀.left // x ∈ closedPoints X₀.left})
    (hZ : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left}), x ∉ Z →
      ∀ r : ℕ, 1 ≤ r →
        complexClosedPowerTrace D l X₀ K x r = complexClosedPowerTrace D l X₀ L x r)
    (a C : ℝ)
    (hE : ∀ n : ℕ, 1 ≤ n →
      (∑ᶠ x : {x : X₀.left // x ∈ closedPoints X₀.left},
        if localClosedPointDegree D X₀ x ∣ n then
          (localClosedPointDegree D X₀ x : ℝ) *
            ‖ι (complexClosedPowerTrace D l X₀ K x (n / localClosedPointDegree D X₀ x) -
              complexClosedPowerTrace D l X₀ L x (n / localClosedPointDegree D X₀ x))‖ ^ 2
        else 0) ≤ C * (D.q : ℝ) ^ ((n : ℝ) * a))
    (hmax : ((a - 1 : ℝ) : EReal) <
      max (growthParameter D l X₀ hl ι K) (growthParameter D l X₀ hl ι L)) :
    growthParameter D l X₀ hl ι K = growthParameter D l X₀ hl ι L := by
  have _ := hZ
  have hKL : growthParameter D l X₀ hl ι K ≤
      max (growthParameter D l X₀ hl ι L) ((a - 1 : ℝ) : EReal) := by
    apply growth_le_max_of_energy_bound D l X₀ hl ι K L a C
    intro n hn
    exact (energy_triangle D l X₀ ι K L n hn).trans
      (by nlinarith [hE n hn])
  have hLK : growthParameter D l X₀ hl ι L ≤
      max (growthParameter D l X₀ hl ι K) ((a - 1 : ℝ) : EReal) := by
    apply growth_le_max_of_energy_bound D l X₀ hl ι L K a C
    intro n hn
    have hs := energy_triangle D l X₀ ι L K n hn
    have he := hE n hn
    have hswap :
        (fun x : {x : X₀.left // x ∈ closedPoints X₀.left} ↦
          if NativeCondensedModule.localClosedPointDegree D X₀ x ∣ n then
            (NativeCondensedModule.localClosedPointDegree D X₀ x : ℝ) *
              ‖ι (complexClosedPowerTrace D l X₀ L x
                  (n / NativeCondensedModule.localClosedPointDegree D X₀ x) -
                complexClosedPowerTrace D l X₀ K x
                  (n / NativeCondensedModule.localClosedPointDegree D X₀ x))‖ ^ 2
          else 0) =
        (fun x : {x : X₀.left // x ∈ closedPoints X₀.left} ↦
          if NativeCondensedModule.localClosedPointDegree D X₀ x ∣ n then
            (NativeCondensedModule.localClosedPointDegree D X₀ x : ℝ) *
              ‖ι (complexClosedPowerTrace D l X₀ K x
                  (n / NativeCondensedModule.localClosedPointDegree D X₀ x) -
                complexClosedPowerTrace D l X₀ L x
                  (n / NativeCondensedModule.localClosedPointDegree D X₀ x))‖ ^ 2
          else 0) := by
      funext x
      simp only [map_sub, norm_sub_rev]
    rw [hswap] at hs
    nlinarith
  rcases lt_max_iff.mp hmax with hK | hL
  · have hL' : ((a - 1 : ℝ) : EReal) < growthParameter D l X₀ hl ι L := by
      by_contra hnot
      have := hKL.trans (max_le (le_of_not_gt hnot) le_rfl)
      exact (not_le_of_gt hK) this
    exact le_antisymm (by rwa [max_eq_left hL'.le] at hKL)
      (by rwa [max_eq_left hK.le] at hLK)
  · have hK' : ((a - 1 : ℝ) : EReal) < growthParameter D l X₀ hl ι K := by
      by_contra hnot
      have := hLK.trans (max_le (le_of_not_gt hnot) le_rfl)
      exact (not_le_of_gt hL) this
    exact le_antisymm (by rwa [max_eq_left hL.le] at hKL)
      (by rwa [max_eq_left hK'.le] at hLK)

end WeilConjectures.NativeL2
