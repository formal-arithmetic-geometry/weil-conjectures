/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import WeilConjectures.Mathlib.RingTheory.PowerSeries.EulerFactors
public import WeilConjectures.Mathlib.NumberTheory.ArithmeticFunction.Moebius

@[expose] public section

open PowerSeries

/-!
# Euler products of a degree function, and the counting zeta series

Chapter 3, §5 and §7–8 of `weil_conjectures_chapter3.tex`
(`sec:weil-orbit-euler-product`, `sec:weil-integral-euler-family-packages`,
`sec:weil-literal-integral-realization-promoted`).

All of the Euler-product material of the chapter is an instance of one construction: a
degree function `d : ι → ℕ` with finitely many indices of bounded degree gives a
`T`-adically locally finite family with components `E_{d i} - 1`, and hence an Euler
product `∏^lf_i E_{d i}` over any commutative coefficient ring.

## Main definitions

* `Weil.countingLogSeries` / `Weil.countingZetaSeries` — the series `∑_{n ≥ 1} c_n Tⁿ/n`
  and its exponential, as functions of a counting function `c : ℕ → ℕ`.
* `Weil.eulerFamily` / `Weil.eulerProduct` — the Euler family and Euler product of a
  degree function, over an arbitrary commutative coefficient ring.
* `Weil.groupedEulerFamily` / `Weil.groupedEulerProduct` — the same product grouped by
  degree, `∏^lf_m E_m^{a_m}`, for a multiplicity function `a : ℕ → ℕ` with `a 0 = 0`.
* `Weil.FiniteOrbitFrobeniusData.orbitEulerProduct` /
  `Weil.FiniteOrbitFrobeniusData.degreeEulerProduct` — the two Euler products attached
  to a finite-orbit Frobenius datum.

## Main results

* `Weil.eulerProduct_eq_groupedEulerProduct` — an Euler product equals its regrouping by
  degree.
* `Weil.map_eulerProduct` / `Weil.map_groupedEulerProduct` — both products commute with
  coefficientwise ring maps, so the rational and the integral realizations of the same
  product are images of one another.
* `Weil.FiniteOrbitFrobeniusData.formalLog_orbitEulerProduct` — `Log(Z_{orb,D}) = S_D`.
* `Weil.FiniteOrbitFrobeniusData.countingZetaSeries_eq_orbitEulerProduct` and
  `Weil.FiniteOrbitFrobeniusData.orbitEulerProduct_eq_degreeEulerProduct` — the counting
  zeta series is the orbit Euler product, and it regroups by degree.
* `Weil.FiniteOrbitFrobeniusData.countingZetaSeries_integralLift` — the counting zeta
  series is the image of the integral orbit Euler product in `ℤ⟦T⟧`; the integrality of
  its coefficients (`hasCoefficientsIn_countingZetaSeries`) is a consequence.
-/

namespace Weil

noncomputable section

/-! ### The counting zeta series of a counting function -/

/-- The counting logarithm series `S ∈ ℚ⟦T⟧` of a counting function `c`, with `[T^0]S = 0` and
`[T^n]S = c_n/n` for `n ≥ 1`. (blueprint: `def:weil-counting-log-series`) -/
def countingLogSeries (c : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n ↦ if n = 0 then 0 else (c n : ℚ) / (n : ℚ)

/-- Coefficients of the counting logarithm.
(blueprint: `lemma:weil-counting-log-series-coeff`) -/
@[simp]
theorem coeff_countingLogSeries (c : ℕ → ℕ) (n : ℕ) :
    coeff n (countingLogSeries c) = if n = 0 then 0 else (c n : ℚ) / (n : ℚ) :=
  coeff_mk _ _

/-- The counting logarithm has positive order.
(blueprint: `lemma:weil-counting-log-series-positive`) -/
@[simp]
theorem constantCoeff_countingLogSeries (c : ℕ → ℕ) :
    constantCoeff (countingLogSeries c) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_countingLogSeries, if_pos rfl]

/-- The exponential counting zeta series `Z_cnt = Exp(S)` of a counting function; the familiar
`Exp(∑_{n ≥ 1} c_n Tⁿ/n)` is only coefficientwise shorthand for this definition.
(blueprint: `def:weil-counting-zeta-series`) -/
def countingZetaSeries (c : ℕ → ℕ) : ℚ⟦X⟧ :=
  formalExp (countingLogSeries c)

/-- The counting zeta series is normalized.
(blueprint: `lemma:weil-counting-zeta-series-constant`) -/
@[simp]
theorem constantCoeff_countingZetaSeries (c : ℕ → ℕ) :
    constantCoeff (countingZetaSeries c) = 1 :=
  constantCoeff_formalExp (constantCoeff_countingLogSeries c)

/-- The counting zeta series only depends on the positive-index values of the counting function.
(blueprint: `lemma:weil-counting-zeta-series-congr`) -/
theorem countingZetaSeries_congr {c c' : ℕ → ℕ} (h : ∀ n, 1 ≤ n → c n = c' n) :
    countingZetaSeries c = countingZetaSeries c' := by
  have hS : countingLogSeries c = countingLogSeries c' := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_countingLogSeries, coeff_countingLogSeries, if_pos rfl, if_pos rfl]
    · rw [coeff_countingLogSeries, coeff_countingLogSeries,
        if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = 0), h n hn]
  rw [countingZetaSeries, countingZetaSeries, hS]

/-! ### The Euler family of a degree function -/

section EulerFamily

variable (R : Type*) [CommRing R] {ι : Type*} (d : ι → ℕ)

/-- The raw Euler-factor family of a degree function, with component `E_{d i} - 1 ∈ R⟦T⟧`.
(blueprint: `def:weil-euler-factor-family`) -/
def eulerFactorFamily (i : ι) : R⟦X⟧ :=
  inverseEulerFactorPositivePart R (d i)

/-- Every Euler factor has constant coefficient zero.
(blueprint: `lemma:weil-euler-factor-family-positive`) -/
@[simp]
theorem constantCoeff_eulerFactorFamily (i : ι) :
    constantCoeff (eulerFactorFamily R d i) = 0 :=
  constantCoeff_inverseEulerFactorPositivePart (d i)

/-- If `N < d i`, then the `i`-th Euler factor agrees with zero through `N`.
(blueprint: `lemma:weil-euler-factor-family-initial-vanishing`) -/
theorem agreeThrough_eulerFactorFamily_zero {i : ι} {N : ℕ} (hNd : N < d i) :
    PowerSeries.AgreeThrough N (eulerFactorFamily R d i) 0 :=
  agreeThrough_inverseEulerFactorPositivePart_zero hNd

/-- If `1 ≤ d i ≤ N`, then the `i`-th Euler factor does not agree with zero through `N`.
(blueprint: `lemma:weil-euler-factor-family-activation`) -/
theorem not_agreeThrough_eulerFactorFamily_zero [Nontrivial R] {i : ι} {N : ℕ}
    (hd : 1 ≤ d i) (hdN : d i ≤ N) :
    ¬ PowerSeries.AgreeThrough N (eulerFactorFamily R d i) 0 :=
  not_agreeThrough_inverseEulerFactorPositivePart_zero hd hdN

/-- If only finitely many indices have degree at most `N`, then only finitely many Euler factors
are active at `N`. (blueprint: `lemma:weil-euler-factor-family-locally-finite`) -/
theorem finite_setOf_not_agreeThrough_eulerFactorFamily
    (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) (N : ℕ) :
    {i : ι | ¬ PowerSeries.AgreeThrough N (eulerFactorFamily R d i) 0}.Finite :=
  (hfin N).subset fun _ hi ↦
    not_lt.mp fun h ↦ hi (agreeThrough_eulerFactorFamily_zero R d h)

/-- The locally finite Euler family `𝓔_d` of a degree function with finite bounded-degree
fibers. (blueprint: `def:weil-euler-locally-finite-family`) -/
def eulerFamily (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) :
    TAdicallyLocallyFiniteFamily R ι where
  toFun := eulerFactorFamily R d
  constantCoeff_eq_zero := constantCoeff_eulerFactorFamily R d
  finite_active := finite_setOf_not_agreeThrough_eulerFactorFamily R d hfin

@[simp]
theorem eulerFamily_toFun (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) (i : ι) :
    (eulerFamily R d hfin).toFun i = eulerFactorFamily R d i :=
  rfl

/-- The Euler product `∏^lf_i E_{d i}` of a degree function.
(blueprint: `def:weil-euler-product`) -/
def eulerProduct (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) : R⟦X⟧ :=
  (eulerFamily R d hfin).product

/-- An Euler product has constant coefficient one.
(blueprint: `lemma:weil-euler-product-constant`) -/
@[simp]
theorem constantCoeff_eulerProduct (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) :
    constantCoeff (eulerProduct R d hfin) = 1 :=
  (eulerFamily R d hfin).constantCoeff_product

/-- Over a nontrivial ring the active indices at level `N` are exactly the indices of degree at
most `N`. (blueprint: `lemma:weil-euler-active-finset`) -/
theorem mem_activeFinset_eulerFamily [Nontrivial R] (hd : ∀ i, 1 ≤ d i)
    (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) {N : ℕ} {i : ι} :
    i ∈ (eulerFamily R d hfin).activeFinset N ↔ d i ≤ N := by
  rw [TAdicallyLocallyFiniteFamily.mem_activeFinset, eulerFamily_toFun]
  refine ⟨fun h ↦ not_lt.mp fun hlt ↦ h (agreeThrough_eulerFactorFamily_zero R d hlt),
    fun h ↦ not_agreeThrough_eulerFactorFamily_zero R d (hd i) h⟩

/-- An Euler product has the prescribed finite truncations: it agrees through `N` with the
finite product over any finset containing all indices of degree at most `N`.
(blueprint: `lemma:weil-euler-product-agree-bounded-product`) -/
theorem agreeThrough_eulerProduct_prod (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) {N : ℕ}
    {S : Finset ι} (hS : ∀ i, d i ≤ N → i ∈ S) :
    PowerSeries.AgreeThrough N (eulerProduct R d hfin)
      (∏ i ∈ S, inverseEulerFactor R (d i)) := by
  have hsub : (eulerFamily R d hfin).activeFinset N ⊆ S := by
    intro i hi
    rw [TAdicallyLocallyFiniteFamily.mem_activeFinset] at hi
    exact hS i (not_lt.mp fun hlt ↦ hi (agreeThrough_eulerFactorFamily_zero R d hlt))
  have h := (eulerFamily R d hfin).product_agree_finset hsub
  have hfac : ∀ i ∈ S, (1 : R⟦X⟧) + (eulerFamily R d hfin).toFun i =
      inverseEulerFactor R (d i) :=
    fun i _ ↦ one_add_inverseEulerFactorPositivePart (d i)
  rwa [Finset.prod_congr rfl hfac] at h

/-- The Euler family of a degree function is compatible with coefficientwise ring maps.
(blueprint: `lemma:weil-euler-family-map`) -/
theorem map_eulerFamily {S : Type*} [CommRing S] (f : R →+* S)
    (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) :
    (eulerFamily R d hfin).map f = eulerFamily S d hfin :=
  TAdicallyLocallyFiniteFamily.ext fun i ↦ map_inverseEulerFactorPositivePart f (d i)

/-- Euler products are compatible with coefficientwise ring maps.
(blueprint: `lemma:weil-euler-product-map`) -/
theorem map_eulerProduct {S : Type*} [CommRing S] (f : R →+* S)
    (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) :
    PowerSeries.map f (eulerProduct R d hfin) = eulerProduct S d hfin := by
  rw [eulerProduct, (eulerFamily R d hfin).product_map f, map_eulerFamily]
  rfl

/-- An Euler product only depends on the degree function up to reindexing along an equivalence.
(blueprint: `lemma:weil-euler-product-reindex`) -/
theorem eulerProduct_comp_equiv {κ : Type*} (e : κ ≃ ι)
    (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite)
    (hfin' : ∀ N : ℕ, {j : κ | (d ∘ e) j ≤ N}.Finite) :
    eulerProduct R (d ∘ e) hfin' = eulerProduct R d hfin := by
  have hre : (eulerFamily R d hfin).reindex e = eulerFamily R (d ∘ e) hfin' := by
    ext j
    rfl
  calc eulerProduct R (d ∘ e) hfin'
      = ((eulerFamily R d hfin).reindex e).product := by rw [hre, eulerProduct]
    _ = eulerProduct R d hfin := (eulerFamily R d hfin).product_reindex e

/-- An Euler product only depends on the degree function.
(blueprint: `lemma:weil-euler-product-congr`) -/
theorem eulerProduct_congr {d' : ι → ℕ} (h : d = d')
    (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite)
    (hfin' : ∀ N : ℕ, {i : ι | d' i ≤ N}.Finite) :
    eulerProduct R d hfin = eulerProduct R d' hfin' := by
  subst h
  rfl

end EulerFamily

/-! ### Euler products grouped by degree -/

section GroupedEulerFamily

variable (R : Type*) [CommRing R] (a : ℕ → ℕ)

/-- The raw degree-grouped Euler-factor family with component `E_m^{a_m} - 1 ∈ R⟦T⟧`.
(blueprint: `def:weil-degree-euler-factor-family`) -/
def groupedEulerFactorFamily (m : ℕ) : R⟦X⟧ :=
  inverseEulerFactor R m ^ a m - 1

/-- Every degree-grouped Euler factor has constant coefficient zero.
(blueprint: `lemma:weil-degree-euler-factor-family-positive`) -/
theorem constantCoeff_groupedEulerFactorFamily (ha : a 0 = 0) (m : ℕ) :
    constantCoeff (groupedEulerFactorFamily R a m) = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [groupedEulerFactorFamily, ha, pow_zero, sub_self, map_zero]
  · rw [groupedEulerFactorFamily, map_sub, map_one, map_pow,
      constantCoeff_inverseEulerFactor hm, one_pow, sub_self]

/-- If `N < m`, then the `m`-th degree-grouped Euler factor agrees with zero through `N`.
(blueprint: `lemma:weil-degree-euler-factor-family-initial-vanishing`) -/
theorem agreeThrough_groupedEulerFactorFamily_zero {m N : ℕ} (hNm : N < m) :
    PowerSeries.AgreeThrough N (groupedEulerFactorFamily R a m) 0 := by
  have hE : PowerSeries.AgreeThrough N (inverseEulerFactor R m) 1 := by
    have h := PowerSeries.AgreeThrough.one_add
      (agreeThrough_inverseEulerFactorPositivePart_zero (R := R) hNm)
    rwa [one_add_inverseEulerFactorPositivePart] at h
  have hpow := hE.pow (a m)
  rw [one_pow] at hpow
  have hsub := hpow.sub (PowerSeries.AgreeThrough.refl N 1)
  rwa [sub_self] at hsub

/-- For every `N` only finitely many degrees are active.
(blueprint: `lemma:weil-degree-euler-factor-family-locally-finite`) -/
theorem finite_setOf_not_agreeThrough_groupedEulerFactorFamily (N : ℕ) :
    {m : ℕ | ¬ PowerSeries.AgreeThrough N (groupedEulerFactorFamily R a m) 0}.Finite :=
  (Set.finite_le_nat N).subset fun _ hm ↦
    not_lt.mp fun h ↦ hm (agreeThrough_groupedEulerFactorFamily_zero R a h)

/-- The degree-grouped Euler family `𝓖_a` of a multiplicity function with `a 0 = 0`.
(blueprint: `def:weil-degree-euler-locally-finite-family`) -/
def groupedEulerFamily (ha : a 0 = 0) : TAdicallyLocallyFiniteFamily R ℕ where
  toFun := groupedEulerFactorFamily R a
  constantCoeff_eq_zero := constantCoeff_groupedEulerFactorFamily R a ha
  finite_active := finite_setOf_not_agreeThrough_groupedEulerFactorFamily R a

@[simp]
theorem groupedEulerFamily_toFun (ha : a 0 = 0) (m : ℕ) :
    (groupedEulerFamily R a ha).toFun m = groupedEulerFactorFamily R a m :=
  rfl

/-- The degree-grouped Euler product `∏^lf_m E_m^{a_m}`.
(blueprint: `def:weil-degree-euler-product`) -/
def groupedEulerProduct (ha : a 0 = 0) : R⟦X⟧ :=
  (groupedEulerFamily R a ha).product

/-- The degree-grouped Euler product is normalized.
(blueprint: `lemma:weil-degree-euler-product-constant`) -/
@[simp]
theorem constantCoeff_groupedEulerProduct (ha : a 0 = 0) :
    constantCoeff (groupedEulerProduct R a ha) = 1 :=
  (groupedEulerFamily R a ha).constantCoeff_product

/-- The degree-grouped Euler product has the bounded-degree truncations.
(blueprint: `lemma:weil-degree-euler-product-agree-bounded-product`) -/
theorem agreeThrough_groupedEulerProduct_prod (ha : a 0 = 0) (N : ℕ) :
    PowerSeries.AgreeThrough N (groupedEulerProduct R a ha)
      (∏ m ∈ Finset.range (N + 1), inverseEulerFactor R m ^ a m) := by
  have hsub : (groupedEulerFamily R a ha).activeFinset N ⊆ Finset.range (N + 1) := by
    intro m hm
    rw [TAdicallyLocallyFiniteFamily.mem_activeFinset] at hm
    rw [Finset.mem_range]
    have hmN : m ≤ N :=
      not_lt.mp fun h ↦ hm (agreeThrough_groupedEulerFactorFamily_zero R a h)
    omega
  have h := (groupedEulerFamily R a ha).product_agree_finset hsub
  have hfac : ∀ m ∈ Finset.range (N + 1),
      (1 : R⟦X⟧) + (groupedEulerFamily R a ha).toFun m = inverseEulerFactor R m ^ a m := by
    intro m _
    rw [groupedEulerFamily_toFun, groupedEulerFactorFamily]
    ring
  rwa [Finset.prod_congr rfl hfac] at h

/-- The degree-grouped Euler family is compatible with coefficientwise ring maps.
(blueprint: `lemma:weil-degree-euler-family-map`) -/
theorem map_groupedEulerFamily {S : Type*} [CommRing S] (f : R →+* S) (ha : a 0 = 0) :
    (groupedEulerFamily R a ha).map f = groupedEulerFamily S a ha :=
  TAdicallyLocallyFiniteFamily.ext fun m ↦ by
    rw [TAdicallyLocallyFiniteFamily.map_toFun, groupedEulerFamily_toFun,
      groupedEulerFamily_toFun, groupedEulerFactorFamily, groupedEulerFactorFamily, map_sub,
      map_one, map_pow, map_inverseEulerFactor]

/-- Degree-grouped Euler products are compatible with coefficientwise ring maps.
(blueprint: `lemma:weil-degree-euler-product-map`) -/
theorem map_groupedEulerProduct {S : Type*} [CommRing S] (f : R →+* S) (ha : a 0 = 0) :
    PowerSeries.map f (groupedEulerProduct R a ha) = groupedEulerProduct S a ha := by
  rw [groupedEulerProduct, (groupedEulerFamily R a ha).product_map f, map_groupedEulerFamily]
  rfl

end GroupedEulerFamily

/-- Regrouping an Euler product by degree: if `F m` is the fiber of the degree function over `m`
and `a m` its cardinality, then `∏^lf_i E_{d i} = ∏^lf_m E_m^{a_m}`.
(blueprint: `prop:weil-euler-product-grouped`) -/
theorem eulerProduct_eq_groupedEulerProduct (R : Type*) [CommRing R] {ι : Type*}
    (d : ι → ℕ) (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) (F : ℕ → Finset ι)
    (hF : ∀ (m : ℕ) (i : ι), i ∈ F m ↔ d i = m) (a : ℕ → ℕ) (hcard : ∀ m, (F m).card = a m)
    (ha : a 0 = 0) :
    eulerProduct R d hfin = groupedEulerProduct R a ha := by
  classical
  ext N
  have hdisj : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint F := by
    intro m _ m' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    exact hne (((hF m i).mp hi).symm.trans ((hF m' i).mp hi'))
  have hsub : ∀ i, d i ≤ N → i ∈ (Finset.range (N + 1)).biUnion F := fun i hi ↦
    Finset.mem_biUnion.mpr
      ⟨d i, Finset.mem_range.mpr (by omega), (hF (d i) i).mpr rfl⟩
  have hgroup : ∏ i ∈ (Finset.range (N + 1)).biUnion F, inverseEulerFactor R (d i) =
      ∏ m ∈ Finset.range (N + 1), inverseEulerFactor R m ^ a m := by
    rw [Finset.prod_biUnion hdisj]
    refine Finset.prod_congr rfl fun m _ ↦ ?_
    calc ∏ i ∈ F m, inverseEulerFactor R (d i)
        = ∏ _i ∈ F m, inverseEulerFactor R m :=
          Finset.prod_congr rfl fun i hi ↦ by rw [(hF m i).mp hi]
      _ = inverseEulerFactor R m ^ a m := by rw [Finset.prod_const, hcard m]
  rw [agreeThrough_eulerProduct_prod R d hfin hsub N le_rfl,
    agreeThrough_groupedEulerProduct_prod R a ha N N le_rfl, hgroup]

/-! ### The logarithm of an Euler product -/

/-- Coefficient of the logarithm of a rational Euler product: for `n ≥ 1`, `[Tⁿ]Log(∏^lf_i E_{d
i}) = (1/n) ∑_{d i ∣ n} d i`, the sum being taken over any finset of the indices of degree
dividing `n`. (blueprint: `prop:weil-log-euler-product`) -/
theorem coeff_formalLog_eulerProduct {ι : Type*} (d : ι → ℕ) (hd : ∀ i, 1 ≤ d i)
    (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) {n : ℕ} (hn : 1 ≤ n) {S : Finset ι}
    (hS : ∀ i, i ∈ S ↔ d i ∣ n) :
    coeff n (formalLog (eulerProduct ℚ d hfin)) = 1 / (n : ℚ) * ∑ i ∈ S, (d i : ℚ) := by
  have hterm : ∀ i : ι, coeff n (formalLog (1 + (eulerFamily ℚ d hfin).toFun i)) =
      if d i ∣ n then (d i : ℚ) / (n : ℚ) else 0 := by
    intro i
    have hlog : formalLog (inverseEulerFactor ℚ (d i)) = eulerLogSeries (d i) :=
      formalLog_normalizedInverseEulerFactor (hd i)
    rw [eulerFamily_toFun, eulerFactorFamily, one_add_inverseEulerFactorPositivePart, hlog,
      coeff_eulerLogSeries]
    by_cases hdvd : d i ∣ n
    · rw [if_pos ⟨by omega, hdvd⟩, if_pos hdvd, one_div_natCast_div (hd i) (by omega) hdvd]
    · rw [if_neg fun hc ↦ hdvd hc.2, if_neg hdvd]
  calc coeff n (formalLog (eulerProduct ℚ d hfin))
      = ∑ i ∈ (eulerFamily ℚ d hfin).activeFinset n,
          coeff n (formalLog (1 + (eulerFamily ℚ d hfin).toFun i)) := by
        rw [eulerProduct, (eulerFamily ℚ d hfin).coeff_formalLog_product n,
          TAdicallyLocallyFiniteFamily.logSum, coeff_mk]
    _ = ∑ i ∈ (eulerFamily ℚ d hfin).activeFinset n,
          (if d i ∣ n then (d i : ℚ) / (n : ℚ) else 0) :=
        Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = ∑ i ∈ S, (if d i ∣ n then (d i : ℚ) / (n : ℚ) else 0) := by
        refine (Finset.sum_subset (fun i hi ↦ ?_) fun i _ hi ↦ ?_).symm
        · rw [mem_activeFinset_eulerFamily ℚ d hd hfin]
          exact Nat.le_of_dvd (by omega) ((hS i).mp hi)
        · rw [if_neg fun hdvd ↦ hi ((hS i).mpr hdvd)]
    _ = ∑ i ∈ S, (d i : ℚ) / (n : ℚ) :=
        Finset.sum_congr rfl fun i hi ↦ if_pos ((hS i).mp hi)
    _ = 1 / (n : ℚ) * ∑ i ∈ S, (d i : ℚ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### The Euler products of a finite-orbit Frobenius datum -/

namespace FiniteOrbitFrobeniusData

variable (D : FiniteOrbitFrobeniusData)

/-- Only finitely many Frobenius orbits have bounded degree.
(blueprint: `lemma:weil-orbit-degree-bounded-finite`) -/
theorem finite_setOf_degree_le (N : ℕ) : {O : D.Orbit | Orbit.degree O ≤ N}.Finite :=
  Set.Finite.subset (D.boundedOrbitFinset N).finite_toSet fun _ hO ↦
    Finset.mem_coe.mpr ((D.mem_boundedOrbitFinset _).mpr hO)

/-- There is no Frobenius orbit of degree zero. (blueprint: `lemma:weil-orbit-count-zero`) -/
@[simp]
theorem orbitCount_zero : D.orbitCount 0 = 0 := by
  rw [orbitCount, Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem fun O hO ↦ ?_
  have h := (D.mem_degreeOrbitFinset O).mp hO
  have := O.degree_pos
  omega

/-- The orbit Euler product `Z_{orb,D} = ∏^lf_O E_{deg_F(O)}`.
(blueprint: `def:weil-orbit-euler-product`) -/
def orbitEulerProduct (R : Type*) [CommRing R] : R⟦X⟧ :=
  eulerProduct R Orbit.degree D.finite_setOf_degree_le

/-- The degree-grouped Euler product `Z_{deg,D} = ∏^lf_m E_m^{a_m(D)}`.
(blueprint: `def:weil-orbit-degree-euler-product`) -/
def degreeEulerProduct (R : Type*) [CommRing R] : R⟦X⟧ :=
  groupedEulerProduct R D.orbitCount D.orbitCount_zero

/-- The orbit Euler product has constant coefficient one.
(blueprint: `lemma:weil-orbit-euler-product-constant`) -/
@[simp]
theorem constantCoeff_orbitEulerProduct (R : Type*) [CommRing R] :
    constantCoeff (D.orbitEulerProduct R) = 1 :=
  constantCoeff_eulerProduct R _ _

/-- Regrouping the orbit Euler product by degree: `Z_{orb,D} = Z_{deg,D}` over every commutative
coefficient ring. (blueprint: `prop:weil-orbit-euler-product-grouped`) -/
theorem orbitEulerProduct_eq_degreeEulerProduct (R : Type*) [CommRing R] :
    D.orbitEulerProduct R = D.degreeEulerProduct R :=
  eulerProduct_eq_groupedEulerProduct R Orbit.degree D.finite_setOf_degree_le
    D.degreeOrbitFinset (fun _ O ↦ D.mem_degreeOrbitFinset O) D.orbitCount
    (fun _ ↦ rfl) D.orbitCount_zero

/-- The logarithm of the orbit Euler product is the counting logarithm: `Log(Z_{orb,D}) = S_D`.
(blueprint: `prop:weil-log-orbit-euler-product`) -/
theorem formalLog_orbitEulerProduct :
    formalLog (D.orbitEulerProduct ℚ) = countingLogSeries D.fixedPointCount := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coeff_zero_eq_constantCoeff_apply,
      constantCoeff_formalLog (D.constantCoeff_orbitEulerProduct ℚ), coeff_countingLogSeries,
      if_pos rfl]
  · rw [orbitEulerProduct,
      coeff_formalLog_eulerProduct Orbit.degree (fun O ↦ O.degree_pos)
        D.finite_setOf_degree_le hn (S := D.relevantOrbitFinset n)
        (D.mem_relevantOrbitFinset hn),
      coeff_countingLogSeries, if_neg (by omega : ¬ n = 0)]
    have h := congrArg (fun k : ℕ ↦ (k : ℚ)) (D.fixedPointCount_eq_sum_degree hn)
    push_cast at h
    rw [h]
    ring

/-- The counting zeta series is the orbit Euler product: `Z_{cnt,D} = Z_{orb,D}`.
(blueprint: `thm:weil-orbit-euler-exponential`) -/
theorem countingZetaSeries_eq_orbitEulerProduct :
    countingZetaSeries D.fixedPointCount = D.orbitEulerProduct ℚ := by
  have h := congrArg formalExp D.formalLog_orbitEulerProduct
  rw [formalExp_formalLog (D.constantCoeff_orbitEulerProduct ℚ)] at h
  exact h.symm

/-- `cor:weil-orbit-zeta-three-forms`, degree-grouped form. The counting zeta series is the
degree-grouped Euler product. (blueprint: `cor:weil-orbit-zeta-degree-form`) -/
theorem countingZetaSeries_eq_degreeEulerProduct :
    countingZetaSeries D.fixedPointCount = D.degreeEulerProduct ℚ :=
  D.countingZetaSeries_eq_orbitEulerProduct.trans (D.orbitEulerProduct_eq_degreeEulerProduct ℚ)

/-! ### The integral realization -/

/-- The rational orbit Euler product is the image of the integral one.
(blueprint: `lemma:weil-integer-orbit-euler-product-map`) -/
theorem map_orbitEulerProduct :
    PowerSeries.map (algebraMap ℤ ℚ) (D.orbitEulerProduct ℤ) = D.orbitEulerProduct ℚ :=
  map_eulerProduct ℤ Orbit.degree (algebraMap ℤ ℚ) D.finite_setOf_degree_le

/-- The rational degree-grouped Euler product is the image of the integral one.
(blueprint: `lemma:weil-integer-degree-euler-product-map`) -/
theorem map_degreeEulerProduct :
    PowerSeries.map (algebraMap ℤ ℚ) (D.degreeEulerProduct ℤ) = D.degreeEulerProduct ℚ :=
  map_groupedEulerProduct ℤ D.orbitCount (algebraMap ℤ ℚ) D.orbitCount_zero

/-- Integral lift of the counting zeta series: `Z_{cnt,D}` is the image of the integral orbit
Euler product `Z_{orb,D}^ℤ ∈ ℤ⟦T⟧`. (blueprint: `prop:weil-counting-zeta-integral-lift`) -/
theorem countingZetaSeries_integralLift :
    PowerSeries.map (algebraMap ℤ ℚ) (D.orbitEulerProduct ℤ) =
      countingZetaSeries D.fixedPointCount := by
  rw [D.map_orbitEulerProduct, D.countingZetaSeries_eq_orbitEulerProduct]

/-- Integrality of the counting zeta series: every coefficient of `Z_{cnt,D}` lies in the image
of `ℤ` in `ℚ`; this is a consequence of the integral lift.
(blueprint: `cor:weil-counting-zeta-integral`) -/
theorem hasCoefficientsIn_countingZetaSeries :
    PowerSeries.HasCoefficientsIn (countingZetaSeries D.fixedPointCount)
      (algebraMap ℤ ℚ).range := fun n ↦
  ⟨coeff n (D.orbitEulerProduct ℤ), by rw [← D.countingZetaSeries_integralLift, coeff_map]⟩

end FiniteOrbitFrobeniusData

end

end Weil
