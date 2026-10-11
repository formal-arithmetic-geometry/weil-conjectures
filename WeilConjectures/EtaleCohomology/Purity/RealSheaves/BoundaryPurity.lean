/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryConstruction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Restriction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity

/-!
# Purity of a lisse sheaf extends over the missing points of a dense open

Let `𝒢` be a lisse Weil sheaf on a smooth geometrically connected curve `C₀` over `𝔽_q`, and
`U₀ ⊆ C₀` a nonempty open on which `𝒢` is punctually `ι`-pure of weight `w`. Then `𝒢` is
punctually `ι`-pure of weight `w` on all of `C₀` (the consequence in
`cor-wf-unramified-boundary-purity`, and the second assertion of `sk-p-real-semi`).

The argument is the one of `lem-wf-boundary-semicontinuity`, for the lisse sheaf `𝒢 = j_* j^* 𝒢`
(`lem-a1-lisse-middle-extension`), whose boundary stalks are its own stalks. On an affine
neighbourhood `X'₀` of a closed point `s`, the Euler product of `𝒢` (`cor-rp-euler-product`)
splits into the Euler series over the closed points of `X'₀ ∩ U₀` and the finitely many local
factors at the points of `X'₀ \ U₀`:

`L (X'₀ ∩ U₀, 𝒢, T) · ι det (1 - F T ∣ H_c²) = P · ∏_{s ∈ X'₀ \ U₀} ι P_s (𝒢, T ^ e_s)`.

The inverse of the open part converges on the disc of radius `q ^ (-(w / 2 + 1))`
(`AlgebraicGeometry.WeilGroup.le_radius_inv_tprod_eulerFactor`), and so does
`P / ι det (1 - F T ∣ H_c²)`, the eigenvalues on `H_c² = V_{π₁}(-1)` being bounded through a
single closed point of `U₀`. So the local polynomials at the points of `X'₀ \ U₀` have no zero
in that disc (`AlgebraicGeometry.WeilGroup.le_norm_of_mul_eq_mul`), which bounds the weights there
by `w + 2`. Tensor squares sharpen the bound to `w`, and the dual gives the lower bound.

## Main statements

- `AlgebraicGeometry.WeilGroup.le_norm_of_mul_eq_mul`: the analytic step, for any identity
  `L (T, ℱ, T) · ι det (1 - F T ∣ H) = P · B` with `B` a polynomial.
- `AlgebraicGeometry.WeilGroup.frobeniusWeight_le_of_isAffine`: on an affine curve, weights at
  most `β` at the closed points of a cofinite set give weights at most `β` everywhere.
- `AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_forall_mem_range`: punctual purity on a
  nonempty open gives punctual purity on the whole curve.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped PowerSeries.WithPiTopology NNReal ENNReal

namespace AlgebraicGeometry.WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

/-- The eigenvalues of the geometric Frobenius on `H_c² (U, ℱ) = V_{π₁(U)} (-1)` are bounded by
`q ^ (β / 2 + 1)` as soon as `ℱ` has weights at most `β` at a single closed point `x`.

Since `π₁(U)` acts trivially on the coinvariants, the local Frobenius `F_x` of degree `e` acts on
them as `γ ^ e`. If `μ` is an eigenvalue of `q γ`, then `(μ / q) ^ e` is an eigenvalue of `F_x` on
the quotient `V_{π₁(U)}` of `V`, hence of `F_x` on `V`, so it has weight at most `β`. -/
theorem norm_le_of_hasEigenvalue_compactTopFrobenius_of_forall (x : C.finitePoints) {β : ℝ}
    (hw : ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β)
    {μ : PadicAlgCl l} (hμ : (W.compactTopFrobenius l ρ).HasEigenvalue μ) :
    ‖ι μ‖ ≤ (Nat.card K : ℝ) ^ (β / 2 + 1) := by
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq : 1 < q := by
    have := (Finite.one_lt_card_iff_nontrivial (α := K)).2 inferInstance
    rw [hqdef]
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqK : (Nat.card K : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  set G := W.geometric
  set Q := ρ.toCoinvariants G
  set T := Q W.frobeniusLift
  set c := μ / (Nat.card K : PadicAlgCl l)
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simp only [map_zero, norm_zero]
    positivity
  -- `c` is an eigenvalue of `γ` on the coinvariants
  have hc : Module.End.HasEigenvalue T c := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    have h := hv.apply_eq_smul
    rw [compactTopFrobenius, LinearMap.smul_apply] at h
    calc T v = (Nat.card K : PadicAlgCl l)⁻¹ • ((Nat.card K : PadicAlgCl l) • T v) := by
          rw [smul_smul, inv_mul_cancel₀ hqK, one_smul]
      _ = c • v := by rw [h, smul_smul, inv_mul_eq_div]
  -- the local Frobenius at `x` acts on the coinvariants as `γ ^ e`
  set e := p.degreeOver x.1
  have he : e ≠ 0 := p.degreeOver_ne_zero x.2
  have htriv (g : W.carrier) (hg : g ∈ G) : Q g = 1 :=
    (inferInstance : Representation.IsTrivial (Q.comp G.subtype)).out ⟨g, hg⟩
  have hn : W.frobenius x * (W.frobeniusLift ^ e)⁻¹ ∈ G := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, W.deg_frobenius, W.deg_frobeniusLift,
      ← ofAdd_nsmul, nsmul_one, mul_inv_eq_one]
  have hQx : Q (W.frobenius x) = T ^ e := by
    rw [show W.frobenius x = (W.frobenius x * (W.frobeniusLift ^ e)⁻¹) * W.frobeniusLift ^ e
      by group, map_mul, htriv _ hn, one_mul, map_pow]
  have hce : Module.End.HasEigenvalue (Q (W.frobenius x)) (c ^ e) := by
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw.2⟩
    rw [Module.End.mem_eigenspace_iff, hQx]
    exact hw.pow_apply e
  -- hence `c ^ e` is a local eigenvalue of `ρ` at `x`
  have hρx : Module.End.HasEigenvalue (ρ (W.frobenius x)) (c ^ e) :=
    Module.End.hasEigenvalue_of_comp_eq_comp (ρ (W.frobenius x)) (Q (W.frobenius x))
      (Representation.Coinvariants.mk _) (Representation.Coinvariants.mk_surjective _)
      (LinearMap.ext fun v ↦ rfl) hce
  have hmem : c ^ e ∈ W.localEigenvalues l ρ x := by
    rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hρx
  have hc0 : c ≠ 0 := div_ne_zero hμ0 hqK
  have hwt := hw _ hmem
  rw [frobeniusWeight_le_iff ι (C.one_lt_pointNorm x.2) ((map_ne_zero ι).2 (pow_ne_zero _ hc0)),
    Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2] at hwt
  -- `|ι c| ≤ q ^ (β / 2)`
  have hcle : ‖ι c‖ ≤ q ^ (β / 2) := by
    have h1 : ‖ι c‖ ^ (2 * e) ≤ (q ^ (β / 2)) ^ (2 * e) := by
      calc ‖ι c‖ ^ (2 * e) = ‖ι (c ^ e)‖ ^ 2 := by rw [map_pow, norm_pow, ← pow_mul, mul_comm]
        _ ≤ _ := hwt
        _ = (q ^ (β / 2)) ^ (2 * e) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast (q ^ (β / 2)), ← Real.rpow_mul hq0.le,
            ← Real.rpow_natCast q e, ← Real.rpow_mul hq0.le]
          push_cast
          ring_nf
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity)
      (mul_ne_zero two_ne_zero he)).1 h1
  have hμc : ‖ι μ‖ = q * ‖ι c‖ := by
    rw [show μ = (Nat.card K : PadicAlgCl l) * c by simp only [c]; field_simp, map_mul, norm_mul,
      map_natCast, Complex.norm_natCast]
  rw [hμc, Real.rpow_add hq0, Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_right hcle hq0.le

variable {W l ρ ι}

/-- The analytic step of `lem-wf-boundary-semicontinuity` (Steps 1–3).

Let `T` be a set of closed points with at most `A q ^ e` points of degree `e`, at which `ℱ` has
weights at most `β`, and suppose that the Euler series of `ℱ` over `T` satisfies
`L (T, ℱ, T) · ∏_{c ∈ S} (1 - c T) = P · B` for polynomials `P` and `B`, where every `c ∈ S`
has `|c| ≤ q ^ (β / 2 + 1)`. Then `B` has no zero in the disc of radius `R = q ^ (-(β / 2 + 1))`.

Indeed `B⁻¹ = (P / ∏ (1 - c T)) · L (T, ℱ, T)⁻¹`, and both factors converge on that disc
(`PowerSeries.le_radius_coe_mul_inv_prod`,
`AlgebraicGeometry.WeilGroup.le_radius_inv_tprod_eulerFactor`). -/
theorem le_norm_of_mul_eq_mul (T : Set C.finitePoints) {β : ℝ}
    (hw : ∀ x ∈ T, ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β)
    {A : ℝ} (hA : ∀ (s : Finset T) (e : ℕ),
      ((s.filter fun x ↦ p.degreeOver x.1.1 = e).card : ℝ) ≤ A * (Nat.card K : ℝ) ^ e)
    {S : Multiset ℂ} (hS : ∀ c ∈ S, ‖c‖ ≤ (Nat.card K : ℝ) ^ (β / 2 + 1))
    {P B : Polynomial ℂ} (hB0 : B.coeff 0 ≠ 0)
    (hP : (∏' x : T, W.eulerFactor l ρ ι x.1) *
      (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod = P * B)
    {z : ℂ} (hz : B.eval z = 0) :
    (Nat.card K : ℝ) ^ (-(β / 2 + 1)) ≤ ‖z‖ := by
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; exact_mod_cast Nat.card_pos (α := K)
  set R : ℝ := q ^ (-(β / 2 + 1))
  have hR : 0 < R := Real.rpow_pos_of_pos hq0 _
  have hRq : q ^ (β / 2 + 1) * R = 1 := by
    rw [← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero]
  set L := ∏' x : T, W.eulerFactor l ρ ι x.1
  set Dser : PowerSeries ℂ := (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod
  have hDser0 : PowerSeries.constantCoeff Dser = 1 := by
    rw [map_multiset_prod, Multiset.map_map, Multiset.prod_eq_one fun a ha ↦ by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
      simp]
  have hL0 : PowerSeries.constantCoeff L = 1 := W.constantCoeff_tprod_eulerFactor l ρ ι T
  have hBcoe : PowerSeries.constantCoeff (B : PowerSeries ℂ) ≠ 0 := by
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  -- `B⁻¹ = P D⁻¹ L⁻¹`
  have hBinv : (B : PowerSeries ℂ)⁻¹ = ((P : PowerSeries ℂ) * Dser⁻¹) * L⁻¹ := by
    have hLD : PowerSeries.constantCoeff (L * Dser) ≠ 0 := by
      rw [map_mul, hL0, hDser0, mul_one]
      exact one_ne_zero
    symm
    rw [PowerSeries.eq_inv_iff_mul_eq_one hBcoe]
    calc (P : PowerSeries ℂ) * Dser⁻¹ * L⁻¹ * B = (P * B) * (Dser⁻¹ * L⁻¹) := by ring
      _ = (L * Dser) * (L * Dser)⁻¹ := by rw [← hP, PowerSeries.mul_inv_rev]
      _ = 1 := PowerSeries.mul_inv_cancel _ hLD
  by_contra! hlt
  set r : NNReal := ⟨(‖z‖ + R) / 2, by positivity⟩
  have hzr : ‖z‖ < r := by change ‖z‖ < (‖z‖ + R) / 2; linarith
  have hrR : (r : ℝ) < R := by change (‖z‖ + R) / 2 < R; linarith
  have hr : ∀ c ∈ S, ‖c‖ * r < 1 := fun c hc ↦ by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · calc ‖c‖ * r < ‖c‖ * R := mul_lt_mul_of_pos_left hrR (norm_pos_iff.2 hc0)
        _ ≤ q ^ (β / 2 + 1) * R := mul_le_mul_of_nonneg_right (hS c hc) hR.le
        _ = 1 := hRq
  have h1 : (r : ENNReal) ≤ ((P : PowerSeries ℂ) * Dser⁻¹).radius :=
    PowerSeries.le_radius_coe_mul_inv_prod P S hr
  have h2 : (r : ENNReal) ≤ L⁻¹.radius :=
    W.le_radius_inv_tprod_eulerFactor l ρ ι T hw hA (by
      calc q ^ (β / 2 + 1) * r < q ^ (β / 2 + 1) * R :=
            mul_lt_mul_of_pos_left hrR (by positivity)
        _ = 1 := hRq)
  have h3 : (‖z‖₊ : ENNReal) < ((B : PowerSeries ℂ)⁻¹).radius := by
    rw [hBinv]
    exact lt_of_lt_of_le (by exact_mod_cast hzr)
      ((le_min h1 h2).trans (PowerSeries.min_radius_le_radius_mul _ _))
  exact PowerSeries.eval_ne_zero_of_lt_radius_inv hB0 h3 hz

omit [Finite K] in
/-- A zero `z` of `1 - ι α T ^ e` outside the disc of radius `q ^ (-(β / 2 + 1))` bounds the weight
of `α` relative to `q ^ e` by `β + 2`. -/
theorem frobeniusWeight_le_add_two_of_le_norm [Finite K] {α : PadicAlgCl l} (hα0 : ι α ≠ 0)
    {e : ℕ} (he : e ≠ 0) {z : ℂ} (hz : z ^ e = (ι α)⁻¹) {β : ℝ}
    (hzR : (Nat.card K : ℝ) ^ (-(β / 2 + 1)) ≤ ‖z‖) :
    frobeniusWeight ι (Nat.card K ^ e) α ≤ β + 2 := by
  set q : ℝ := (Nat.card K : ℝ) with hqdef
  have hq : 1 < q := by
    have := (Finite.one_lt_card_iff_nontrivial (α := K)).2 inferInstance
    rw [hqdef]
    exact_mod_cast this
  have hq0 : 0 < q := zero_lt_one.trans hq
  set R : ℝ := q ^ (-(β / 2 + 1))
  have hR : 0 < R := Real.rpow_pos_of_pos hq0 _
  have hnorm : ‖ι α‖ ≤ q ^ ((e : ℝ) * (β / 2 + 1)) := by
    have hze : ‖z‖ ^ e = ‖ι α‖⁻¹ := by rw [← norm_pow, hz, norm_inv]
    have hRe : R ^ e ≤ ‖ι α‖⁻¹ := hze ▸ pow_le_pow_left₀ hR.le hzR e
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le] at hRe
    have := (le_inv_comm₀ (by positivity) (norm_pos_iff.2 hα0)).1 hRe
    rwa [← Real.rpow_neg hq0.le, neg_mul, neg_neg, mul_comm] at this
  rw [frobeniusWeight, Nat.cast_pow, Real.log_pow,
    div_le_iff₀ (mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)) (Real.log_pos hq))]
  have := Real.log_le_log (norm_pos_iff.2 hα0) hnorm
  rw [Real.log_rpow hq0] at this
  change 2 * Real.log ‖ι α‖ ≤ (β + 2) * (e * Real.log q)
  nlinarith

variable (W l ρ ι)

/-- The local polynomial `ι P_x (ℱ, T ^ e_x)` is `1` modulo `T ^ e_x`. -/
theorem X_pow_dvd_coe_localPolynomial_sub_one (x : C.finitePoints) :
    (PowerSeries.X : PowerSeries ℂ) ^ p.degreeOver x.1 ∣
      ((((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ p.degreeOver x.1) :
        Polynomial ℂ) : PowerSeries ℂ) - 1 := by
  have hP : (Polynomial.X : Polynomial ℂ) ∣ (W.localPolynomial l ρ x).map ι - 1 := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_zero_eq_eval_zero,
      eval_zero_map_localPolynomial, Polynomial.coeff_one_zero, sub_self]
  obtain ⟨R, hR⟩ := hP
  have hQ : (Polynomial.X : Polynomial ℂ) ^ p.degreeOver x.1 ∣
      ((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ p.degreeOver x.1) - 1 :=
    ⟨R.comp (Polynomial.X ^ p.degreeOver x.1), by
      rw [← Polynomial.one_comp (p := Polynomial.X ^ _), ← Polynomial.sub_comp, hR,
        Polynomial.mul_comp, Polynomial.X_comp]⟩
  have hQ' := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) hQ
  simpa only [map_pow, map_sub, map_one, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X] using hQ'

/-- The Euler product over any set of closed points converges. -/
theorem multipliable_eulerFactor_subtype (T : Set C.finitePoints) :
    Multipliable fun x : T ↦ W.eulerFactor l ρ ι x.1 :=
  PowerSeries.WithPiTopology.multipliable_inv_of_X_pow_dvd_sub_one
    (e := fun x : T ↦ p.degreeOver x.1.1) (fun x ↦ p.degreeOver_ne_zero x.1.2)
    (fun x ↦ X_pow_dvd_coe_localPolynomial_sub_one W l ρ ι x.1)
    (fun n ↦ (p.finite_setOf_degreeOver_le n).preimage Subtype.val_injective.injOn)

/-- The Euler series splits into the Euler product over a set `T` of closed points with finite
complement and the finitely many local factors at the points outside `T`. -/
theorem eulerSeries_eq_tprod_mul_prod {T : Set C.finitePoints} (hT : Tᶜ.Finite) :
    W.eulerSeries l ρ ι =
      (∏' x : T, W.eulerFactor l ρ ι x.1) * ∏ x ∈ hT.toFinset, W.eulerFactor l ρ ι x := by
  have : Finite ↥Tᶜ := hT.to_subtype
  rw [eulerSeries, ← (W.multipliable_eulerFactor_subtype l ρ ι T).tprod_mul_tprod_compl
    (Multipliable.of_finite), ← Finset.tprod_subtype']
  congr 1
  exact tprod_congr_set_coe _ hT.coe_toFinset.symm

/-- On an affine curve, the closed points of degree `e` number at most `A q ^ e`
(`lem-wf-point-count-linear-growth`), in any finite set of them. -/
theorem exists_card_filter_degreeOver_le_of_isAffine [IsAffine C] :
    ∃ A : ℝ, ∀ (T : Set C.finitePoints) (t : Finset T) (e : ℕ),
      ((t.filter fun x ↦ p.degreeOver x.1.1 = e).card : ℝ) ≤ A * (Nat.card K : ℝ) ^ e := by
  classical
  obtain ⟨d, hd⟩ := p.exists_pointCount_le_mul_pow (IsCurve.krullDim_le_one p)
  refine ⟨d, fun T t e ↦ ?_⟩
  rcases eq_or_ne e 0 with rfl | he
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ ↦
      p.degreeOver_ne_zero x.1.2)]
    simp
  set S := (t.filter fun x ↦ p.degreeOver x.1.1 = e).image Subtype.val
  have hS : S.card = (t.filter fun x ↦ p.degreeOver x.1.1 = e).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  set T' := (p.finite_setOf_degreeOver_le e).toFinset
  have hcount := p.pointCount_eq_sum he (T := T') fun y hy ↦ by
    simpa [T'] using Nat.le_of_dvd (Nat.pos_of_ne_zero he) hy
  have hST : S ⊆ T'.filter fun y ↦ p.degreeOver y.1 ∣ e := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hxe := (Finset.mem_filter.1 hx).2
    simp [T', hxe]
  have hle : S.card ≤ p.pointCount e := by
    rw [hcount]
    calc S.card = ∑ y ∈ S, 1 := by simp
      _ ≤ ∑ y ∈ S, p.degreeOver y.1 := Finset.sum_le_sum fun y _ ↦
          Nat.one_le_iff_ne_zero.2 (p.degreeOver_ne_zero y.2)
      _ ≤ _ := Finset.sum_le_sum_of_subset hST
  rw [← hS]
  exact_mod_cast hle.trans (hd e he)

/-- Steps 0–3 of `lem-wf-boundary-semicontinuity` for a lisse sheaf on an affine curve.

Let `C₀` be a smooth geometrically connected affine curve, `ℱ` lisse on `C₀` and `T` a set of
closed points with finite complement, containing some point `x₀`, at which `ℱ` has weights at
most `β`. Then every local eigenvalue of `ℱ`, at any closed point, has weight at most `β + 2`.

By the Euler product of `ℱ` (`cor-rp-euler-product`), split into the Euler product over `T` and
the local factors at the points outside `T`
(`AlgebraicGeometry.WeilGroup.eulerSeries_eq_tprod_mul_prod`), the product `B` of the local
polynomials outside `T` satisfies `L (T, ℱ, T) · ι det (1 - F T ∣ H_c²) = P · B`. The eigenvalues
on `H_c²` are bounded through the point `x₀`
(`AlgebraicGeometry.WeilGroup.norm_le_of_hasEigenvalue_compactTopFrobenius_of_forall`), so `B`
has no zero in the disc of radius `q ^ (-(β / 2 + 1))`
(`AlgebraicGeometry.WeilGroup.le_norm_of_mul_eq_mul`). -/
theorem frobeniusWeight_le_add_two_of_isAffine [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] (hρ : W.IsLisse l ρ)
    {T : Set C.finitePoints} (hT : Tᶜ.Finite) {x₀ : C.finitePoints} (hx₀ : x₀ ∈ T) {β : ℝ}
    (hw : ∀ x ∈ T, ∀ α ∈ W.localEigenvalues l ρ x, frobeniusWeight ι (C.pointNorm x.1) α ≤ β)
    (s : C.finitePoints) {α : PadicAlgCl l} (hα : α ∈ W.localEigenvalues l ρ s) :
    frobeniusWeight ι (C.pointNorm s.1) α ≤ β + 2 := by
  classical
  by_cases hs : s ∈ T
  · linarith [hw s hs α hα]
  -- the Euler product identity
  obtain ⟨P, hP⟩ := exists_eulerSeries_mul_eq_coe ρ ι hρ
  obtain ⟨A, hA⟩ := exists_card_filter_degreeOver_le_of_isAffine (p := p)
  set lp : C.finitePoints → Polynomial ℂ := fun x ↦
    ((W.localPolynomial l ρ x).map ι).comp (Polynomial.X ^ p.degreeOver x.1)
  set B : Polynomial ℂ := ∏ x ∈ hT.toFinset, lp x
  set S := (W.compactTopFrobenius l ρ).charpoly.roots.map ι
  have hS : ∀ c ∈ S, ‖c‖ ≤ (Nat.card K : ℝ) ^ (β / 2 + 1) := by
    intro c hc
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hc
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hμ
    exact W.norm_le_of_hasEigenvalue_compactTopFrobenius_of_forall l ρ ι x₀ (hw x₀ hx₀) hμ
  have hDser : (((W.compactTopFrobenius l ρ).charpolyRev.map ι : Polynomial ℂ) :
      PowerSeries ℂ) = (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod := by
    rw [LinearMap.charpolyRev_eq_prod_roots, Polynomial.map_multiset_prod_one_sub_C_mul_X,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun c _ ↦ by simp)
  have hlp0 (x : C.finitePoints) : PowerSeries.constantCoeff ((lp x : Polynomial ℂ) :
      PowerSeries ℂ) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_pow,
      Polynomial.eval_X, zero_pow (p.degreeOver_ne_zero x.2), eval_zero_map_localPolynomial]
    exact one_ne_zero
  have hFB : (∏ x ∈ hT.toFinset, W.eulerFactor l ρ ι x) * (B : PowerSeries ℂ) = 1 := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ ↦ PowerSeries.inv_mul_cancel _ (hlp0 x)
  have hP' : (∏' x : T, W.eulerFactor l ρ ι x.1) *
      (S.map fun c ↦ 1 - PowerSeries.C c * PowerSeries.X).prod = P * B := by
    rw [← hDser, ← hP, W.eulerSeries_eq_tprod_mul_prod l ρ ι hT]
    linear_combination -(∏' x : T, W.eulerFactor l ρ ι x.1) *
      (((W.compactTopFrobenius l ρ).charpolyRev.map ι : Polynomial ℂ) : PowerSeries ℂ) * hFB
  have hB0 : B.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun x _ ↦ ?_
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
      zero_pow (p.degreeOver_ne_zero x.2), eval_zero_map_localPolynomial]
    exact one_ne_zero
  -- the zero `z` of the local polynomial at `s`
  set e := p.degreeOver s.1
  have he : e ≠ 0 := p.degreeOver_ne_zero s.2
  have hα0 : ι α ≠ 0 :=
    (map_ne_zero ι).2 fun h ↦ zero_notMem_localEigenvalues (ρ := ρ) s (h ▸ hα)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι α)⁻¹ (Nat.pos_of_ne_zero he)
  have hBz : B.eval z = 0 := by
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero (i := s) (hT.mem_toFinset.2 hs) ?_
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, hz, map_localPolynomial,
      Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨1 - Polynomial.C (ι α) * Polynomial.X,
      Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem ι hα), ?_⟩)
    simp [hα0]
  have hzR := le_norm_of_mul_eq_mul T hw (hA T) hS hB0 hP' hBz
  rw [Scheme.Hom.pointNorm_eq_pow_degreeOver p s.2]
  exact frobeniusWeight_le_add_two_of_le_norm hα0 he hz hzR

end AlgebraicGeometry.WeilGroup
