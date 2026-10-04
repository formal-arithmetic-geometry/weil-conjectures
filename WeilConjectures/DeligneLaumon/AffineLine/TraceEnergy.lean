/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.EReal.Operations
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.DeligneLaumon.AffineLine.Endpoints
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Detecting a weight from the growth of the squared trace sums

For a lisse Weil sheaf `N` on a variety over `𝔽_q` the *trace energy* is the sum of the
squared complex absolute values of its trace function over the `𝔽_{qⁿ}`-points,

`S_n(X₀, N) = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_{N,n}(x)|²`.

Its exponential generating series is the `L`-function of `N ⊗ N^∨(w)` on a curve, hence a
ratio of two determinants, and the denominator is pure of weight `2v + 2` by the endpoint
lemma `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`. The
series has infinitely many nonzero coefficients because the summands are nonnegative and not
all zero, so at least one finite pole survives; an energy bound `S_n ≤ C q^{nB}` forces the
radius of convergence to be at least `q^{-B}`, so that pole cannot lie inside, giving
`v ≤ B - 1`. No weight estimate for `H_c^1` is used.

The proof goes through the `L²`-weight parameter `‖N‖`, the exponent of growth of the trace
energies: the energy bound gives `‖N‖ ≤ B - 1`, and the `L²`-rigidity gives `‖N‖ = v` for a
nonzero lisse punctually pure `N`. The rigidity is deduced from the case of `ι`-real sheaves by
passing to the normalized real envelope `N⁰ ⊕ (N⁰)^∨` of the constant twist `N⁰` of weight `0`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.traceEnergy`: the sum `S_n(X₀, N)`.
- `AlgebraicGeometry.WeilSheaf.l2Weight`: the `L²`-weight parameter `‖F‖`.
- `AlgebraicGeometry.WeilSheaf.l2Series`: the `L²`-series `φ_F(t) = ∑ S_m t^{m - 1}`.
- `AlgebraicGeometry.WeilSheaf.realEnvelope`: the normalized real envelope.
- `AlgebraicGeometry.WeilSheaf.lt_l2Weight_iff`: the radius of `φ_F` is `q^{-‖F‖ - 1}`.
- `AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isPunctuallyPureOfWeight`: `‖G‖ = w` for a nonzero
  lisse sheaf pure of weight `w`.
- `AlgebraicGeometry.WeilSheaf.le_sub_one_of_traceEnergy_le`: the weight bound it detects.

## Implementation notes

With the present coefficients every Weil sheaf is zero (`AlgebraicGeometry.WeilSheaf.isZero`):
trace functions, trace energies and stalks vanish. The statements about traces of twists,
envelopes and tensor products are proved this way, and the statements about a nonzero sheaf
hold vacuously. The analytic part (the `L²`-weight, its radius characterisation and the energy
bound) is proved in general.
-/

@[expose] public section

universe u

open CategoryTheory Filter Topology

open scoped PowerSeries.WithPiTopology

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace energy `S_n(X₀, F) = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_{F,n}(x)|²` of a Weil sheaf at
level `n`, the squared `L²`-norm of its trace function on the `𝔽_{qⁿ}`-points, with junk value
`0` if `X₀` has infinitely many `𝔽_{qⁿ}`-points. The intended situation is that of
`AlgebraicGeometry.Scheme.Hom.finite_fieldPoints`, where `X₀` is of finite type over the finite
field `k₀` and the index type is finite. (blueprint: `sk-l-dl-a1-energy`) -/
noncomputable def traceEnergy (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (n : ℕ) : ℝ :=
  ∑ᶠ x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n),
    ‖ι (F.traceFunction n x)‖ ^ 2

/-- The trace function of a Weil sheaf vanishes: with the present coefficients the stalks are
zero (`AlgebraicGeometry.WeilSheaf.isZero_stalkObj`). -/
theorem traceFunction_eq_zero (F : WeilSheaf k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    F.traceFunction n x = 0 := by
  simp only [traceFunction, Subsingleton.elim _ (0 : Module.End _ _), map_zero]

/-- The trace energy of a Weil sheaf vanishes, its trace function being zero
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_zero`). -/
theorem traceEnergy_eq_zero (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (n : ℕ) :
    F.traceEnergy ι n = 0 := by
  simp [traceEnergy, traceFunction_eq_zero]

/-- The trace energy is nonnegative, as a sum of squares. -/
theorem traceEnergy_nonneg (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (n : ℕ) :
    0 ≤ F.traceEnergy ι n :=
  finsum_nonneg fun _ ↦ sq_nonneg _

/-- The *`L²`-weight parameter* `‖F‖` of a Weil sheaf, the exponent of growth of its trace
energies `S_m = ‖f_F‖²_m` (`AlgebraicGeometry.WeilSheaf.traceEnergy`):

`‖F‖ = sup {β ∈ ℝ | limsup_{m → ∞} S_m / q^{m(β + 1)} > 0}`,

the supremum of the empty set being `-∞`, the exponent `1` being the dimension of the curve on
which `F` is intended to live. The `limsup` is taken in `ℝ≥0∞`.
(blueprint: `def-wf-l2-norm`) -/
noncomputable def l2Weight (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : EReal :=
  ⨆ (β : ℝ) (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
    (F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop), (β : EReal)

/-- The *`L²`-series* `φ_F(t) = ∑_{m ≥ 1} S_m t^{m - 1}` of a Weil sheaf, the power series whose
coefficients are the trace energies `S_m` (`AlgebraicGeometry.WeilSheaf.traceEnergy`). Its
radius of convergence determines the `L²`-weight parameter
(`AlgebraicGeometry.WeilSheaf.lt_l2Weight_iff`).
(blueprint: `def-wf-l2-series`) -/
noncomputable def l2Series (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun m ↦ F.traceEnergy ι (m + 1)

section Growth

/-! ### The exponent of growth of a nonnegative sequence -/

variable {q : ℝ} {b : ℕ → ℝ}

private lemma div_rpow_eq_mul_pow (hq : 0 < q) (m : ℕ) (β : ℝ) :
    b m / q ^ ((m : ℝ) * (β + 1)) = b m * (q ^ (-(β + 1))) ^ m := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, div_eq_mul_inv, ← Real.rpow_neg hq.le]
  congr 2
  ring

private lemma limsup_eq_zero_of_le (hq : 1 < q) {C B : ℝ}
    (hb : ∀ m : ℕ, 1 ≤ m → b m ≤ C * q ^ ((m : ℝ) * B)) {β : ℝ} (hβ : B - 1 < β) :
    limsup (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop = 0 := by
  have hq0 : 0 < q := by linarith
  have hr1 : q ^ (B - (β + 1)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hlim : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (C * (q ^ (B - (β + 1))) ^ m)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr1).const_mul C
    rw [mul_zero] at h
    simpa using ENNReal.tendsto_ofReal h
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_).limsup_eq
  filter_upwards [eventually_ge_atTop 1] with m hm
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by positivity)]
  calc b m ≤ C * q ^ ((m : ℝ) * B) := hb m hm
    _ = C * (q ^ (B - (β + 1))) ^ m * q ^ ((m : ℝ) * (β + 1)) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
      congr 2
      ring

private lemma radius_le_of_limsup_pos (hq : 1 < q) {β : ℝ}
    (h : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop) :
    (FormalMultilinearSeries.ofScalars ℝ fun n ↦ b (n + 1)).radius ≤
      ENNReal.ofReal (q ^ (-(β + 1))) := by
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 ≤ q ^ (-(β + 1)) := by positivity
  by_contra hlt
  rw [not_le] at hlt
  rw [ENNReal.ofReal_eq_coe_nnreal hρ0] at hlt
  have ht := (Asymptotics.isLittleO_one_iff ℝ).1
    ((FormalMultilinearSeries.ofScalars ℝ fun n ↦ b (n + 1)).isLittleO_one_of_lt_radius hlt)
  simp only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_mk] at ht
  have ht' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (‖b (n + 1)‖ * (q ^ (-(β + 1))) ^ n *
      q ^ (-(β + 1)))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (ht.mul_const (q ^ (-(β + 1))))
  have hs : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop
      (𝓝 0) := by
    refine (tendsto_add_atTop_iff_nat 1).1 (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ht' (fun _ ↦ zero_le) fun n ↦ ENNReal.ofReal_le_ofReal ?_)
    rw [div_rpow_eq_mul_pow hq0, pow_succ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hρ0
  exact h.ne' hs.limsup_eq

private lemma limsup_pos_of_radius_lt (hq : 1 < q) (hb : ∀ m, 0 ≤ b m) {β : ℝ}
    (h : (FormalMultilinearSeries.ofScalars ℝ fun n ↦ b (n + 1)).radius <
      ENNReal.ofReal (q ^ (-(β + 1)))) :
    0 < limsup (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop := by
  have hq0 : 0 < q := by linarith
  have hρ0 : 0 < q ^ (-(β + 1)) := by positivity
  refine pos_iff_ne_zero.2 fun h0 ↦ h.not_ge ?_
  have hev := eventually_lt_of_limsup_lt (h0.trans_lt zero_lt_one)
  rw [ENNReal.ofReal_eq_coe_nnreal hρ0.le]
  refine FormalMultilinearSeries.le_radius_of_eventually_le _ (1 / q ^ (-(β + 1))) ?_
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hev] with n hn
  rw [ENNReal.ofReal_lt_one, div_rpow_eq_mul_pow hq0, pow_succ, ← mul_assoc] at hn
  rw [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_mk, Real.norm_eq_abs,
    abs_of_nonneg (hb _), le_div_iff₀ hρ0]
  exact hn.le

private lemma limsup_eq_zero_of_le_mul (hq : 0 ≤ q) {b' : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ m, b' m ≤ K * b m) {β : ℝ}
    (h : limsup (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop = 0) :
    limsup (fun m : ℕ ↦ ENNReal.ofReal (b' m / q ^ ((m : ℝ) * (β + 1)))) atTop = 0 := by
  have ht : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (b m / q ^ ((m : ℝ) * (β + 1)))) atTop
      (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le zero_le h.le
  have ht' := ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal K)
  rw [mul_zero] at ht'
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht'
    (fun _ ↦ zero_le) fun m ↦ ?_).limsup_eq
  rw [← ENNReal.ofReal_mul hK, mul_div_assoc']
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb m) (Real.rpow_nonneg hq _))

end Growth

/-- The trace energy bound `S_m ≤ C q^{mB}` for `m ≥ 1` bounds the `L²`-weight parameter:
`‖F‖ ≤ B - 1`. For `β > B - 1` the ratios `S_m / q^{m(β + 1)} ≤ C q^{m(B - β - 1)}` tend to
`0`. -/
theorem l2Weight_le_of_traceEnergy_le (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    {C B : ℝ} (hS : ∀ n : ℕ, 1 ≤ n → F.traceEnergy ι n ≤ C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * B)) :
    F.l2Weight ι ≤ ((B - 1 : ℝ) : EReal) := by
  refine iSup₂_le fun β hβ ↦ EReal.coe_le_coe_iff.2 (not_lt.1 fun hlt ↦ hβ.ne' ?_)
  exact limsup_eq_zero_of_le (by exact_mod_cast Finite.one_lt_card) hS hlt

/-- The radius of convergence `r_F` of the `L²`-series `φ_F` and the `L²`-weight parameter
`‖F‖` are related by `r_F = q^{-‖F‖ - 1}`, equivalently `‖F‖ = -1 - log_q r_F`, with the
conventions `q^{-∞} = 0` and `q^{∞} = ∞`. This is stated as: for every real `β`,
`β < ‖F‖` if and only if `r_F < q^{-(β + 1)}`. (blueprint: `lem-wf-l2-radius`) -/
theorem lt_l2Weight_iff (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (β : ℝ) :
    (β : EReal) < F.l2Weight ι ↔
      (F.l2Series ι).radius < ENNReal.ofReal ((Nat.card k₀ : ℝ) ^ (-(β + 1))) := by
  have hq : 1 < (Nat.card k₀ : ℝ) := by exact_mod_cast Finite.one_lt_card
  have hq0 : 0 < (Nat.card k₀ : ℝ) := by linarith
  constructor
  · intro h
    obtain ⟨β', h'⟩ := lt_iSup_iff.1 h
    obtain ⟨hpos, hlt⟩ := lt_iSup_iff.1 h'
    refine (radius_le_of_limsup_pos hq hpos).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (by positivity)).2 (Real.rpow_lt_rpow_of_exponent_lt hq ?_))
    linarith [EReal.coe_lt_coe_iff.1 hlt]
  · intro h
    have hc : Tendsto (fun x : ℝ ↦ ENNReal.ofReal ((Nat.card k₀ : ℝ) ^ (-(x + 1)))) (𝓝[>] β)
        (𝓝 (ENNReal.ofReal ((Nat.card k₀ : ℝ) ^ (-(β + 1))))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.rpow (by fun_prop)
        fun _ ↦ Or.inl hq0.ne')).tendsto β).mono_left nhdsWithin_le_nhds
    obtain ⟨β', hβ'r, hββ'⟩ := ((hc.eventually (lt_mem_nhds h)).and self_mem_nhdsWithin).exists
    exact (EReal.coe_lt_coe_iff.2 hββ').trans_le (le_iSup₂_of_le β'
      (limsup_pos_of_radius_lt hq (F.traceEnergy_nonneg ι) hβ'r) le_rfl)

/-- If the trace energies of `F'` are those of `F` divided by `q^{mw}`, then
`‖F'‖ = ‖F‖ - w`: the defining ratio of `F'` at `β` is that of `F` at `β + w`. -/
theorem l2Weight_eq_sub_of_traceEnergy_eq (ι : PadicAlgCl l →+* ℂ) (F F' : WeilSheaf k₀ l X)
    {w : ℝ} (h : ∀ m : ℕ, F'.traceEnergy ι m =
      F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w)) :
    F'.l2Weight ι = F.l2Weight ι - w := by
  have hq0 : 0 < (Nat.card k₀ : ℝ) := by exact_mod_cast Nat.card_pos
  have key : ∀ β : ℝ, (fun m : ℕ ↦ ENNReal.ofReal
      (F'.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) =
      fun m : ℕ ↦ ENNReal.ofReal
        (F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * ((β + w) + 1))) := by
    refine fun β ↦ funext fun m ↦ congrArg ENNReal.ofReal ?_
    rw [h, div_div, ← Real.rpow_add hq0]
    congr 2
    ring
  refine le_antisymm (iSup₂_le fun β hβ ↦ ?_) ?_
  · rw [key] at hβ
    rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot w)) (.inl (EReal.coe_ne_top w))]
    exact_mod_cast le_iSup₂_of_le (f := fun (γ : ℝ) _ ↦ (γ : EReal)) (β + w) hβ le_rfl
  · rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot w)) (.inl (EReal.coe_ne_top w))]
    refine iSup₂_le fun γ hγ ↦ ?_
    have hγ' : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
        (F'.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * ((γ - w) + 1)))) atTop := by
      rwa [key, sub_add_cancel]
    have := le_iSup₂_of_le (f := fun (β : ℝ) (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
        (F'.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop) ↦ (β : EReal))
      (γ - w) hγ' le_rfl
    calc (γ : EReal) = ((γ - w : ℝ) : EReal) + w := by norm_cast; ring
      _ ≤ F'.l2Weight ι + w := by gcongr; exact this

/-- If the trace energies of `E` are bounded by a constant multiple of those of `F`, then
`‖E‖ ≤ ‖F‖`: a positive `limsup` for `E` at `β` forces a positive `limsup` for `F` at `β`. -/
theorem l2Weight_le_of_traceEnergy_le_mul (ι : PadicAlgCl l →+* ℂ) (E F : WeilSheaf k₀ l X)
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ m : ℕ, E.traceEnergy ι m ≤ K * F.traceEnergy ι m) :
    E.l2Weight ι ≤ F.l2Weight ι :=
  iSup₂_le fun β hβ ↦ le_iSup₂_of_le β
    (pos_iff_ne_zero.2 fun h0 ↦ hβ.ne' (limsup_eq_zero_of_le_mul (Nat.cast_nonneg _) hK h h0))
    le_rfl

section Envelope

/-- The *normalized real envelope* `Env_ι(F; b) = F⁰ ⊕ (F⁰)^∨` of a Weil sheaf, where
`F⁰ = F ⊗ 𝓑_b` is the constant Weil twist `AlgebraicGeometry.WeilSheaf.constantTwist` by
`b`. It is meant for `F` punctually `ι`-pure of weight `w` and `|ι b| = q^{-w/2}`, for instance
`b = ι⁻¹(q^{-w/2})` when `ι` is an isomorphism; then `F⁰` is pure of weight `0` and the
envelope is `ι`-real (`AlgebraicGeometry.WeilSheaf.isReal_realEnvelope`).
(blueprint: `def-wf-normalized-real-envelope`) -/
noncomputable def realEnvelope (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) : WeilSheaf k₀ l X :=
  F.constantTwist b ⊞ (F.constantTwist b).dual

/-- The stalks of a Weil sheaf at closed points are zero, see
`AlgebraicGeometry.WeilSheaf.isZero_stalkObj`. -/
instance subsingleton_stalk_carrier (F : WeilSheaf k₀ l X) (x : X.finitePoints) :
    Subsingleton (F.stalk x).carrier :=
  subsingleton_stalkAt_carrier _ _ _ _

/-- The local polynomials of a Weil sheaf are `1`, its stalks being zero
(`AlgebraicGeometry.WeilSheaf.isZero_stalkObj`). -/
theorem localPolynomial_stalk_eq_one (F : WeilSheaf k₀ l X) (x : X.finitePoints) :
    (F.stalk x).localPolynomial = 1 := by
  rw [FrobeniusModule.localPolynomial, LinearMap.charpolyRev_def,
    LinearMap.charpoly_eq_one_of_subsingleton]
  simpa using Polynomial.reverse_C (1 : PadicAlgCl l)

-- with the present coefficients the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- If `F` is lisse and punctually `ι`-pure of weight `w` and `2 log_q |ι b| = c`, then the
constant twist `F ⊗ 𝓑_b` is punctually `ι`-pure of weight `w + c`: at a closed point of degree
`m` every eigenvalue `α` of the local Frobenius becomes `bᵐ α`, of absolute value
`q^{mc/2} q^{mw/2}`. (blueprint: `lem-wf-constant-twist-weight`) -/
theorem IsPunctuallyPureOfWeight.constantTwist {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ} {c : ℝ}
    (hb : 2 * Real.logb (Nat.card k₀) ‖ι b‖ = c) :
    (F.constantTwist b).IsPunctuallyPureOfWeight ι (w + c) := by
  -- with the present coefficients the stalks are zero, so there are no eigenvalues
  intro x α hα
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  exact (hv.2 (Subsingleton.elim _ _)).elim

-- with the present coefficients the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- The envelope `Env_ι(F; b)` of a lisse sheaf `F` punctually `ι`-pure of weight `w`, with
`|ι b| = q^{-w/2}`, is `ι`-real: at a closed point the eigenvalues `β_j` of `F⁰` have
`|ι β_j| = 1`, so those of the dual summand are `ι(β_j⁻¹) = conj (ι β_j)`, and the local
eigenvalue multiset is stable under complex conjugation.
(blueprint: `lem-wf-envelope-real`) -/
theorem isReal_realEnvelope {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X} {w : ℝ}
    (h : F.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) :
    (F.realEnvelope b).IsReal ι := by
  -- with the present coefficients the stalks are zero, so the local polynomials are `1`
  intro x n
  rw [localPolynomial_stalk_eq_one, Polynomial.coeff_one]
  split_ifs <;> simp

-- with the present coefficients the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- The envelope of a punctually `ι`-pure sheaf of weight `w`, with `|ι b| = q^{-w/2}`, is
punctually `ι`-pure of weight `0`: `F⁰` is by
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.constantTwist`, its dual has the inverse
eigenvalues, of absolute value `1`, and a direct sum of pure sheaves of weight `0` is pure of
weight `0`. -/
theorem IsPunctuallyPureOfWeight.realEnvelope {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) :
    (F.realEnvelope b).IsPunctuallyPureOfWeight ι 0 := by
  -- with the present coefficients the stalks are zero, so there are no eigenvalues
  intro x α hα
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  exact (hv.2 (Subsingleton.elim _ _)).elim

-- with the present coefficients the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- The trace energies of the constant twist `F ⊗ 𝓑_b` with `|ι b| = q^{-w/2}` are those of `F`
divided by `q^{mw}`: the twist has trace function `t_{F ⊗ 𝓑_b}(y) = bᵐ t_F(y)` at
`y ∈ X₀(𝔽_{qᵐ})`. -/
theorem traceEnergy_constantTwist (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X)
    {b : (PadicAlgCl l)ˣ} {w : ℝ} (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) (m : ℕ) :
    (F.constantTwist b).traceEnergy ι m =
      F.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * w) := by
  -- with the present coefficients both trace functions are zero
  simp [traceEnergy_eq_zero]

-- with the present coefficients the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- The trace energies of the envelope are at most four times those of `F⁰ = F ⊗ 𝓑_b`, for `F`
punctually pure of weight `w` and `|ι b| = q^{-w/2}`: the trace of the envelope is
`t_{F⁰} + conj t_{F⁰} = 2 Re t_{F⁰}`, and `|Re z|² ≤ |z|²`. -/
theorem traceEnergy_realEnvelope_le (ι : PadicAlgCl l →+* ℂ) {F : WeilSheaf k₀ l X} {w : ℝ}
    (h : F.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2)) (m : ℕ) :
    (F.realEnvelope b).traceEnergy ι m ≤ 4 * (F.constantTwist b).traceEnergy ι m := by
  -- with the present coefficients both trace functions are zero
  simp [traceEnergy_eq_zero]

/-- A nonzero lisse Weil sheaf, punctually `ι`-pure of weight `w`, admits a unit `b` with
`|ι b| = q^{-w/2}`: if `α` is an eigenvalue of the local Frobenius at a closed point of degree
`d` with nonzero stalk, then `|ι α| = q^{dw/2}`, and `b` can be taken to be a `d`-th root of
`α⁻¹`. -/
theorem exists_norm_eq_of_isPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ)
    (F : WeilSheaf k₀ l X) (hF : ¬ Limits.IsZero F) {w : ℝ}
    (h : F.IsPunctuallyPureOfWeight ι w) :
    ∃ b : (PadicAlgCl l)ˣ, ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-w / 2) := by
  -- a nonzero Weil sheaf has a nonzero stalk at some closed point; with the present
  -- coefficients there is no nonzero Weil sheaf (`AlgebraicGeometry.WeilSheaf.isZero`)
  obtain ⟨x, hx⟩ : ∃ x : X.finitePoints, Nontrivial (F.stalk x).carrier :=
    (hF F.isZero).elim
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (F.stalk x).frobeniusEnd
  have hα0 : α ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, zero_smul] at hv
    exact hv.2 ((F.stalk x).frobenius.map_eq_zero_iff.1 hv.1)
  set d := (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  have hd : 0 < d := by
    have : Finite (X.residueField x.1) := x.2
    let := ((X ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap x.1).toAlgebra
    have : Module.Finite k₀ (X.residueField x.1) := Module.Finite.of_finite
    exact Module.finrank_pos
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq α⁻¹ hd
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hα0 (by rw [← hc, zero_pow hd.ne'])
  refine ⟨Units.mk0 c hc0, ?_⟩
  have hq0 : 0 < (Nat.card k₀ : ℝ) := by exact_mod_cast Nat.card_pos
  have hαn := h x α hα
  simp only [Scheme.Hom.residueCard, Nat.cast_pow] at hαn
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) hd.ne').1 ?_
  rw [Units.val_mk0, ← norm_pow, ← map_pow, hc, map_inv₀, norm_inv, hαn, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le, ← Real.rpow_neg hq0.le]
  congr 1
  ring

end Envelope

-- with the present coefficients the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- The `L²`-weight is at most the weight: if `F` is a lisse Weil sheaf on the smooth
geometrically connected affine curve `X₀`, punctually `ι`-mixed of weights at most `w`, then
`‖F‖ ≤ w`. At `y ∈ X₀(𝔽_{qᵐ})` the eigenvalues of the Frobenius have absolute value at most
`q^{mw/2}`, so `S_m ≤ r² · #X₀(𝔽_{qᵐ}) · q^{mw} ≤ C q^{m(w + 1)}`, and
`AlgebraicGeometry.WeilSheaf.l2Weight_le_of_traceEnergy_le` applies.
(blueprint: `lem-wf-l2-upper`) -/
theorem l2Weight_le_of_hasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l V) (hlisse : F.IsLisse) {w : ℝ} (h : F.HasWeightsAtMost ι w) :
    F.l2Weight ι ≤ w := by
  -- with the present coefficients the trace energies vanish, so the bound holds with `C = 0`
  have := F.l2Weight_le_of_traceEnergy_le ι (C := 0) (B := w + 1)
    fun n _ ↦ by simp [traceEnergy_eq_zero]
  simpa using this

/-- The `L`-series `L(X₀, F, t) = ∏_{x ∈ |X₀|} det(1 - Fₓ t^{d(x)} | F_x̄)⁻¹ ∈ ℂ⟦t⟧` of a Weil
sheaf, the product over the closed points of `X₀` of the inverses of the local polynomials
`FrobeniusModule.localPolynomial` of the stalks, transported to `ℂ` along `ι` and substituted
into `t^{d(x)}` for the degree `d(x) = [κ(x) : k₀]`. It is taken in the product topology on
`ℂ⟦t⟧`, in which it converges for `X₀` of finite type over `k₀`. -/
noncomputable def lSeries (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : PowerSeries ℂ :=
  ∏' x : X.finitePoints, ((((F.stalk x).localPolynomial.map ι).comp
    (Polynomial.X ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial ℂ) :
      PowerSeries ℂ)⁻¹

-- with the present coefficients the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- Let `F` be a lisse Weil sheaf on the smooth geometrically connected affine curve `X₀` and
`F'` a Weil sheaf whose local eigenvalues are the complex conjugates of those of `F` (the sheaf
`F̄` of the complex-conjugate local Frobenius eigenvalues), in that the local polynomials of
`F'` are the conjugates of those of `F` under `ι`. Then at every `y ∈ X₀(𝔽_{qᵐ})`

`ι Tr(F_y | (F ⊗ F̄)_ȳ) = |ι Tr(F_y | F_ȳ)|² ≥ 0`,

and consequently the `L²`-series `φ_F(t) = ∑_{m ≥ 1} S_m t^{m - 1}` is the logarithmic
derivative `L'/L` of the `L`-series `L(X₀, F ⊗ F̄, t)`
(`AlgebraicGeometry.WeilSheaf.lSeries`), the Euler-product form of the Grothendieck–Lefschetz
trace formula: `φ_F · L = L'`. (blueprint: `lem-wf-conjugate-tensor-traces`) -/
theorem traceFunction_tensorObj_and_l2Series_mul_lSeries (ι : PadicAlgCl l →+* ℂ)
    {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (F F' : WeilSheaf k₀ l V) (hlisse : F.IsLisse)
    (hconj : ∀ x : V.finitePoints, (F'.stalk x).localPolynomial.map ι =
      ((F.stalk x).localPolynomial.map ι).map (starRingEnd ℂ)) :
    (∀ (n : ℕ) (y : (V ↘ Spec (CommRingCat.of k₀)).fieldPoints
        (FiniteField.galoisExtension k₀ n)),
      ι ((F.tensorObj F').traceFunction n y) = ((‖ι (F.traceFunction n y)‖ ^ 2 : ℝ) : ℂ)) ∧
    PowerSeries.mk (fun m ↦ (F.traceEnergy ι (m + 1) : ℂ)) * (F.tensorObj F').lSeries ι =
      PowerSeries.derivative ℂ ((F.tensorObj F').lSeries ι) := by
  -- with the present coefficients all stalks are zero: the trace functions vanish and every
  -- local factor of the `L`-series is `1`
  have hL : (F.tensorObj F').lSeries ι = 1 := by
    refine (tprod_congr fun x ↦ ?_).trans tprod_one
    rw [localPolynomial_stalk_eq_one, Polynomial.map_one,
      Polynomial.one_comp, Polynomial.coe_one, inv_one]
  refine ⟨fun n y ↦ by simp [traceFunction_eq_zero], ?_⟩
  rw [hL, Derivation.map_one_eq_zero, mul_one]
  ext
  simp [traceEnergy_eq_zero]

-- with the present coefficients the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- The *`L²`-rigidity* for real sheaves: let `G` be a nonzero lisse `ι`-real Weil sheaf on the
smooth geometrically connected affine curve `X₀`, punctually `ι`-pure of weight `w`. Then
`‖G‖ = w`.

The proof in the blueprint writes `φ_G = L'/L` with `L` the ratio of the determinants of the
Frobenius on `H_c¹` and `H_c²` of `G ⊗ G`; the denominator is pure of weight `2w + 2` by the
endpoint lemma, positivity of the local factors forces a surviving pole on `|t| = q^{-w-1}`,
and the radius `q^{-w-1}` gives `‖G‖ = w` by `AlgebraicGeometry.WeilSheaf.lt_l2Weight_iff`.
With the present coefficients every Weil sheaf is zero (`AlgebraicGeometry.WeilSheaf.isZero`),
so the hypothesis `G ≠ 0` cannot hold. (blueprint: `thm-wf-l2-dictionary`) -/
theorem l2Weight_eq_of_isReal (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l V) (hG : ¬ Limits.IsZero G) (hlisse : G.IsLisse) (hreal : G.IsReal ι)
    {w : ℝ} (hpure : G.IsPunctuallyPureOfWeight ι w) :
    G.l2Weight ι = w :=
  (hG G.isZero).elim

/-- The *`L²`-weight of a punctually pure lisse sheaf equals its weight*: let `G` be a nonzero
lisse Weil sheaf on the smooth geometrically connected affine curve `X₀`, punctually `ι`-pure
of weight `w`. Then `‖G‖ = w`; the reality hypothesis of
`AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isReal` is not needed.

The twist `G⁰ = G ⊗ 𝓑_b` with `|ι b| = q^{-w/2}` has `‖G⁰‖ = ‖G‖ - w`; its envelope `E` is
real and pure of weight `0`, so `‖E‖ = 0`; the traces of `E` are `2 Re t_{G⁰}`, so
`‖E‖ ≤ ‖G⁰‖`; and `‖G⁰‖ ≤ 0` by `AlgebraicGeometry.WeilSheaf.l2Weight_le_of_hasWeightsAtMost`.
(blueprint: `lem-wf-l2-purity-rigidity`) -/
theorem l2Weight_eq_of_isPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l V) (hG : ¬ Limits.IsZero G) (hlisse : G.IsLisse) {w : ℝ}
    (hpure : G.IsPunctuallyPureOfWeight ι w) :
    G.l2Weight ι = w := by
  obtain ⟨b, hb⟩ := G.exists_norm_eq_of_isPunctuallyPureOfWeight ι hG hpure
  have hq : 1 < (Nat.card k₀ : ℝ) := by exact_mod_cast Finite.one_lt_card
  have hc : 2 * Real.logb (Nat.card k₀) ‖ι b‖ = -w := by
    rw [hb, Real.logb_rpow (by linarith) hq.ne']
    ring
  -- Step 1: the twist shifts the `L²`-weight by `w`
  have h1 : (G.constantTwist b).l2Weight ι = G.l2Weight ι - w :=
    l2Weight_eq_sub_of_traceEnergy_eq ι G _ (traceEnergy_constantTwist ι G hb)
  -- Step 2: the envelope has `L²`-weight zero
  have h2 : (G.realEnvelope b).l2Weight ι = 0 := by
    -- with the present coefficients the envelope, like `G`, cannot be shown to be nonzero
    -- or lisse other than through the vacuous hypothesis `G ≠ 0`
    have hE : ¬ Limits.IsZero (G.realEnvelope b) := (hG G.isZero).elim
    have hElisse : (G.realEnvelope b).IsLisse := (hG G.isZero).elim
    exact_mod_cast l2Weight_eq_of_isReal ι _ hE hElisse (isReal_realEnvelope hpure hb)
      (hpure.realEnvelope hb)
  -- Step 3: comparison with the envelope
  have h3 : (G.realEnvelope b).l2Weight ι ≤ (G.constantTwist b).l2Weight ι :=
    l2Weight_le_of_traceEnergy_le_mul ι _ _ (by norm_num)
      (traceEnergy_realEnvelope_le ι hpure hb)
  have h4 : (G.constantTwist b).l2Weight ι ≤ 0 := by
    have hlisse' : (G.constantTwist b).IsLisse := hlisse
    have := l2Weight_le_of_hasWeightsAtMost ι _ hlisse'
      (hpure.constantTwist hc).hasWeightsAtMost
    simpa using this
  have h0 : G.l2Weight ι - w = 0 := h1 ▸ le_antisymm h4 (h2 ▸ h3)
  have := congrArg (· + (w : EReal)) h0
  simp only [zero_add] at this
  rwa [EReal.sub_add_cancel] at this

-- the hypothesis `0 < C` is not needed for the bound
set_option linter.unusedVariables false in
/-- Let `N ≠ 0` be lisse on a smooth geometrically connected affine curve `V₀` of finite type
over `k₀` and punctually `ι`-pure of weight `v`. If the trace energies satisfy
`S_n(V₀, N) ≤ C q^{nB}` for every `n ≥ 1`, with `0 < C` independent of `n`, then `v ≤ B - 1`.

The energy bound bounds the `L²`-weight parameter `‖N‖` by `B - 1`
(`AlgebraicGeometry.WeilSheaf.l2Weight_le_of_traceEnergy_le`), and `‖N‖ = v` by the
`L²`-rigidity `AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isPunctuallyPureOfWeight`.
(blueprint: `sk-l-dl-a1-energy`) -/
theorem le_sub_one_of_traceEnergy_le (ι : PadicAlgCl l →+* ℂ) {V : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [IsAffine V]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (V ↘ Spec (CommRingCat.of k₀))]
    (N : WeilSheaf k₀ l V) (hN : ¬ Limits.IsZero N) (hlisse : N.IsLisse) {v : ℝ}
    (hpure : N.IsPunctuallyPureOfWeight ι v) {C B : ℝ} (hC : 0 < C)
    (hS : ∀ n : ℕ, 1 ≤ n → N.traceEnergy ι n ≤ C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * B)) :
    v ≤ B - 1 := by
  have h := (l2Weight_eq_of_isPunctuallyPureOfWeight ι N hN hlisse hpure).symm.trans_le
    (N.l2Weight_le_of_traceEnergy_le ι hS)
  exact_mod_cast h

end WeilSheaf

end AlgebraicGeometry
