/-
Formalization of Chapter 3, Section 5 of `weil_conjectures_chapter3.tex`:
"Orbit Euler products and the counting zeta series"
(`sec:weil-orbit-euler-product`).

Every declaration below is annotated with the LaTeX label it formalizes.
Design notes, following the conventions of the earlier section files:

* Per the "Rational coefficient scope" paragraph, the coefficient ring is
  literally `ℚ` throughout: `E_m` is `inverseEulerFactor ℚ m`, and
  `Log`/`Exp` are `formalLog`/`formalExp` of `Weil.FormalExpLog`.
* Since `formalLog`/`formalExp` act on raw power series (with the
  normalization certificates carried by the lemmas, per the design notes of
  `Weil.FormalExpLog`), the bundled objects of the text
  (`normalizedOrbitEulerProduct`, `positiveCountingLogSeries`) are provided
  as stated, while the computation lemmas are phrased on the underlying
  series.
* The two-part statement `lemma:weil-orbit-euler-active-finset` is provided
  as the positive-level component under the tex name together with the
  `N = 0` component `orbitEulerFamily_activeFinset_zero`.
* `lemma:weil-bounded-orbit-product-regroup-by-degree` is proved by
  decomposing `boundedOrbitFinset` as a `Finset.biUnion` of the one-degree
  orbit finsets (the same decomposition used for
  `lemma:weil-relevant-orbits-regroup-by-degree` in `Weil.FrobeniusOrbits`),
  with `lemma:weil-bounded-orbit-degree-fiber` provided as stated.
* In `prop:weil-orbit-euler-product-grouped` the `N = 0` coefficients are
  compared through the generic constant-coefficient formula for locally
  finite products rather than through the empty-index argument of the text.
-/
module

public import WeilConjectures.chap3_power_series.EulerFactors
public import WeilConjectures.chap3_power_series.FrobeniusOrbits

@[expose] public section

open PowerSeries

namespace Weil

noncomputable section

namespace FiniteOrbitFrobeniusData

/-! ### The orbit Euler product and the counting zeta series -/

/-- `def:weil-orbit-euler-factor-family`.  The raw orbit Euler-factor family
`u_O = E_{deg_F(O)} - 1 ∈ ℚ⟦T⟧`. -/
def orbitEulerFactorFamily (D : FiniteOrbitFrobeniusData) (O : D.Orbit) :
    ℚ⟦X⟧ :=
  inverseEulerFactorPositivePart ℚ (Orbit.degree O)

/-- The factor `1 + u_O` is the inverse Euler factor `E_{deg_F(O)}` (inline
unfolding step used repeatedly in the text's proofs). -/
theorem one_add_orbitEulerFactorFamily (D : FiniteOrbitFrobeniusData)
    (O : D.Orbit) :
    1 + D.orbitEulerFactorFamily O = inverseEulerFactor ℚ (Orbit.degree O) := by
  rw [orbitEulerFactorFamily, inverseEulerFactorPositivePart]
  ring

/-- `lemma:weil-orbit-euler-factor-family-positive`.  Every orbit Euler
factor has constant coefficient zero. -/
theorem orbitEulerFactorFamily_positive (D : FiniteOrbitFrobeniusData)
    (O : D.Orbit) :
    constantCoeff (D.orbitEulerFactorFamily O) = 0 :=
  inverseEulerFactorPositivePart_constantCoeff (Orbit.degree O)

/-- If `N < deg_F(O)`, then `u_O ≡_N 0`; specialization of the
initial-vanishing lemma for inverse Euler factors. -/
theorem orbitEulerFactorFamily_agree_zero (D : FiniteOrbitFrobeniusData)
    {O : D.Orbit} {N : ℕ} (hNd : N < Orbit.degree O) :
    PowerSeries.AgreeThrough N (D.orbitEulerFactorFamily O) 0 :=
  inverseEulerFactorPositivePart_agreeThrough hNd

/-- If `deg_F(O) ≤ N`, then `u_O ≢_N 0`; specialization of the activation
lemma for inverse Euler factors. -/
theorem orbitEulerFactorFamily_not_agree_zero (D : FiniteOrbitFrobeniusData)
    {O : D.Orbit} {N : ℕ} (hdN : Orbit.degree O ≤ N) :
    ¬ PowerSeries.AgreeThrough N (D.orbitEulerFactorFamily O) 0 :=
  inverseEulerFactorPositivePart_not_agree_zero O.degree_pos hdN

/-- `lemma:weil-orbit-euler-factor-family-locally-finite`.  For every `N`,
only finitely many orbits have `u_O ≢_N 0`. -/
theorem orbitEulerFactorFamily_locallyFinite (D : FiniteOrbitFrobeniusData)
    (N : ℕ) :
    {O : D.Orbit |
      ¬ PowerSeries.AgreeThrough N (D.orbitEulerFactorFamily O) 0}.Finite := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine Set.Finite.subset Set.finite_empty fun O hO => ?_
    exact absurd (D.orbitEulerFactorFamily_agree_zero O.degree_pos) hO
  · refine Set.Finite.subset (D.boundedOrbitFinset N).finite_toSet fun O hO => ?_
    have hdeg : Orbit.degree O ≤ N := by
      by_contra hlt
      exact hO (D.orbitEulerFactorFamily_agree_zero (by omega))
    exact Finset.mem_coe.mpr ((D.mem_boundedOrbitFinset hN O).mpr hdeg)

/-- `def:weil-orbit-euler-locally-finite-family`.  The packaged locally
finite orbit Euler family `𝓔_D` with index type `Orb_F(Ω)` and component
`u_O = E_{deg_F(O)} - 1`. -/
def orbitEulerFamily (D : FiniteOrbitFrobeniusData) :
    TAdicallyLocallyFiniteFamily ℚ D.Orbit where
  toFun := D.orbitEulerFactorFamily
  constantCoeff_eq_zero := D.orbitEulerFactorFamily_positive
  finite_active := D.orbitEulerFactorFamily_locallyFinite

/-- `def:weil-orbit-euler-product`.  The orbit Euler product
`Z_{orb,D} = ∏^lf_{O} E_{deg_F(O)}`. -/
def orbitEulerProduct (D : FiniteOrbitFrobeniusData) : ℚ⟦X⟧ :=
  D.orbitEulerFamily.product

/-- `lemma:weil-orbit-euler-active-finset`, positive-level part.  For
`N ≥ 1`, the active-index finset of `𝓔_D` is `𝒪_{≤ N}`. -/
theorem orbitEulerFamily_activeFinset (D : FiniteOrbitFrobeniusData) {N : ℕ}
    (hN : 1 ≤ N) :
    D.orbitEulerFamily.activeFinset N = D.boundedOrbitFinset N := by
  ext O
  rw [TAdicallyLocallyFiniteFamily.mem_activeFinset,
    D.mem_boundedOrbitFinset hN O]
  constructor
  · intro h
    by_contra hdeg
    exact h (D.orbitEulerFactorFamily_agree_zero (by omega))
  · exact fun hdeg => D.orbitEulerFactorFamily_not_agree_zero hdeg

/-- `lemma:weil-orbit-euler-active-finset`, `N = 0` part: no orbit Euler
factor is active at truncation level zero. -/
theorem orbitEulerFamily_activeFinset_zero (D : FiniteOrbitFrobeniusData) :
    D.orbitEulerFamily.activeFinset 0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun O hO => ?_
  rw [TAdicallyLocallyFiniteFamily.mem_activeFinset] at hO
  exact hO (D.orbitEulerFactorFamily_agree_zero O.degree_pos)

/-- `lemma:weil-orbit-euler-product-constant`.  The orbit Euler product has
constant coefficient one. -/
theorem orbitEulerProduct_constantCoeff (D : FiniteOrbitFrobeniusData) :
    constantCoeff D.orbitEulerProduct = 1 :=
  D.orbitEulerFamily.product_constantCoeff

/-- `def:weil-bundled-orbit-euler-product`.  The bundled normalized orbit
Euler product `Z¹_{orb,D} ∈ OneSeries(ℚ)`. -/
def normalizedOrbitEulerProduct (D : FiniteOrbitFrobeniusData) : OneSeries ℚ :=
  ⟨D.orbitEulerProduct, D.orbitEulerProduct_constantCoeff⟩

/-- `def:weil-counting-log-series`.  The counting logarithm series
`S_D ∈ ℚ⟦T⟧` with `[T^0]S_D = 0` and `[T^n]S_D = N_n(D)/n` for `n ≥ 1`. -/
def countingLogSeries (D : FiniteOrbitFrobeniusData) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else (D.fixedPointCount n : ℚ) / (n : ℚ)

/-- Coefficient formula of `def:weil-counting-log-series`, restated through
`PowerSeries.coeff_mk` for rewriting. -/
theorem coeff_countingLogSeries (D : FiniteOrbitFrobeniusData) (n : ℕ) :
    coeff n D.countingLogSeries =
      if n = 0 then 0 else (D.fixedPointCount n : ℚ) / (n : ℚ) := by
  rw [countingLogSeries, coeff_mk]

/-- `lemma:weil-counting-log-series-positive`.  The counting logarithm has
positive order. -/
theorem countingLogSeries_positive (D : FiniteOrbitFrobeniusData) :
    constantCoeff D.countingLogSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_countingLogSeries, if_pos rfl]

/-- `def:weil-bundled-counting-log-series`.  The bundled counting logarithm
`S_D⁺ ∈ PositiveSeries(ℚ)`. -/
def positiveCountingLogSeries (D : FiniteOrbitFrobeniusData) :
    PositiveSeries ℚ :=
  ⟨D.countingLogSeries, D.countingLogSeries_positive⟩

/-- `def:weil-counting-zeta-series`.  The exponential counting zeta series
`Z_{cnt,D} = Exp(S_D)`; the familiar `Exp(∑_{n≥1} N_n(D)Tⁿ/n)` is only
coefficientwise shorthand for this definition. -/
def countingZetaSeries (D : FiniteOrbitFrobeniusData) : ℚ⟦X⟧ :=
  formalExp D.countingLogSeries

/-- `lemma:weil-log-orbit-euler-product-coeff`.  Coefficient of the logarithm
of the orbit Euler product: for `n ≥ 1`,
`[Tⁿ]Log(Z_{orb,D}) = (1/n) ∑_{O ∈ 𝒪(n)} deg_F(O)`. -/
theorem coeff_log_orbitEulerProduct (D : FiniteOrbitFrobeniusData) {n : ℕ}
    (hn : 1 ≤ n) :
    coeff n (formalLog D.orbitEulerProduct) =
      1 / (n : ℚ) * ∑ O ∈ D.relevantOrbitFinset n, (Orbit.degree O : ℚ) := by
  classical
  have hterm : ∀ O : D.Orbit,
      coeff n (formalLog (1 + D.orbitEulerFamily.toFun O)) =
        if Orbit.degree O ∣ n then (Orbit.degree O : ℚ) / (n : ℚ) else 0 := by
    intro O
    have hdeg : 1 ≤ Orbit.degree O := O.degree_pos
    have hlog : formalLog (inverseEulerFactor ℚ (Orbit.degree O)) =
        eulerLogSeries (Orbit.degree O) := formalLog_inverseEulerFactor hdeg
    rw [show (1 : ℚ⟦X⟧) + D.orbitEulerFamily.toFun O =
        inverseEulerFactor ℚ (Orbit.degree O) from
      D.one_add_orbitEulerFactorFamily O, hlog, coeff_eulerLogSeries]
    by_cases hdvd : Orbit.degree O ∣ n
    · rw [if_pos ⟨by omega, hdvd⟩, if_pos hdvd,
        one_div_natDiv_cast hdeg (by omega) hdvd]
    · rw [if_neg fun hc => hdvd hc.2, if_neg hdvd]
  calc coeff n (formalLog D.orbitEulerProduct)
      = ∑ O ∈ D.boundedOrbitFinset n,
          coeff n (formalLog (1 + D.orbitEulerFamily.toFun O)) := by
        rw [orbitEulerProduct, D.orbitEulerFamily.coeff_log_product n,
          TAdicallyLocallyFiniteFamily.logSum, coeff_mk,
          D.orbitEulerFamily_activeFinset hn]
    _ = ∑ O ∈ D.boundedOrbitFinset n,
          (if Orbit.degree O ∣ n then (Orbit.degree O : ℚ) / (n : ℚ) else 0) :=
        Finset.sum_congr rfl fun O _ => hterm O
    _ = ∑ O ∈ D.relevantOrbitFinset n,
          (if Orbit.degree O ∣ n then (Orbit.degree O : ℚ) / (n : ℚ) else 0) := by
        refine (Finset.sum_subset (fun O hO => ?_) fun O _ hO => ?_).symm
        · exact (D.mem_boundedOrbitFinset hn O).mpr
            (Nat.le_of_dvd (by omega) ((D.mem_relevantOrbitFinset hn O).mp hO))
        · rw [if_neg fun hd => hO ((D.mem_relevantOrbitFinset hn O).mpr hd)]
    _ = ∑ O ∈ D.relevantOrbitFinset n, (Orbit.degree O : ℚ) / (n : ℚ) :=
        Finset.sum_congr rfl fun O hO =>
          if_pos ((D.mem_relevantOrbitFinset hn O).mp hO)
    _ = 1 / (n : ℚ) * ∑ O ∈ D.relevantOrbitFinset n, (Orbit.degree O : ℚ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun O _ => by ring

/-- `prop:weil-log-orbit-euler-product`.  The logarithm of the orbit Euler
product is the counting logarithm: `Log(Z_{orb,D}) = S_D`. -/
theorem log_orbitEulerProduct (D : FiniteOrbitFrobeniusData) :
    formalLog D.orbitEulerProduct = D.countingLogSeries := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coeff_zero_eq_constantCoeff_apply,
      formalLog_constantCoeff D.orbitEulerProduct_constantCoeff,
      coeff_countingLogSeries, if_pos rfl]
  · rw [D.coeff_log_orbitEulerProduct hn, coeff_countingLogSeries,
      if_neg (by omega : ¬ n = 0)]
    have h := congrArg (fun k : ℕ => (k : ℚ))
      (D.fixedPointCount_eq_sum_orbits hn)
    push_cast at h
    rw [h]
    ring

/-- `thm:weil-orbit-euler-exponential`.  The Euler product equals the
exponential counting series: `Z_{cnt,D} = Z_{orb,D} = ∏^lf_O E_{deg_F(O)}`
(the last product being `def:weil-orbit-euler-product`). -/
theorem orbitEulerProduct_eq_countingZeta (D : FiniteOrbitFrobeniusData) :
    D.countingZetaSeries = D.orbitEulerProduct := by
  have h := congrArg formalExp D.log_orbitEulerProduct
  rw [formalExp_formalLog D.orbitEulerProduct_constantCoeff] at h
  rw [countingZetaSeries]
  exact h.symm

/-- `lemma:weil-orbit-euler-factor-family-integral-coefficients`.  Every
orbit Euler component has coefficients in the image of `ℤ` in `ℚ`. -/
theorem orbitEulerFactorFamily_integralCoefficients
    (D : FiniteOrbitFrobeniusData) (O : D.Orbit) :
    PowerSeries.HasCoefficientsIn (D.orbitEulerFactorFamily O)
      (algebraMap ℤ ℚ).range := by
  intro n
  rw [orbitEulerFactorFamily, inverseEulerFactorPositivePart, map_sub,
    coeff_inverseEulerFactor O.degree_pos, coeff_one]
  refine Subring.sub_mem _ ?_ ?_
  · split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

/-- `cor:weil-counting-zeta-integral`.  Integrality of the counting zeta
series: every coefficient of `Z_{cnt,D}` lies in the image of `ℤ` in `ℚ`. -/
theorem countingZetaSeries_integral (D : FiniteOrbitFrobeniusData) :
    PowerSeries.HasCoefficientsIn D.countingZetaSeries
      (algebraMap ℤ ℚ).range := by
  rw [D.orbitEulerProduct_eq_countingZeta]
  exact D.orbitEulerFamily.product_mem_subring
    D.orbitEulerFactorFamily_integralCoefficients

end FiniteOrbitFrobeniusData

/-! ### Degree-grouped Euler products -/

/-- `def:weil-positive-natural-degree-index`.  The index type
`ℕ_{>0} = {m : ℕ | 1 ≤ m}` of positive natural degrees; its coercion to `ℕ`
is the subtype projection. -/
abbrev PositiveDegreeIndex : Type :=
  {m : ℕ // 1 ≤ m}

/-- `def:weil-positive-degree-index-finset`.  The finset
`I_N⁺ = {m ∈ ℕ_{>0} | (m : ℕ) ≤ N}`, defined by the prescribed
`Finset.preimage` of the interval `Finset.Icc 1 N`. -/
def positiveDegreeIndexFinset (N : ℕ) : Finset PositiveDegreeIndex :=
  (Finset.Icc 1 N).preimage Subtype.val Subtype.val_injective.injOn

/-- `lemma:weil-positive-degree-index-finset-mem`.  Membership in the finite
positive-degree index set. -/
theorem mem_positiveDegreeIndexFinset {N : ℕ} (m : PositiveDegreeIndex) :
    m ∈ positiveDegreeIndexFinset N ↔ (m : ℕ) ≤ N := by
  rw [positiveDegreeIndexFinset, Finset.mem_preimage, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨m.2, h⟩⟩

namespace FiniteOrbitFrobeniusData

/-- `def:weil-degree-euler-factor-family`.  The raw degree-grouped
Euler-factor family `v_m = E_m^{a_m(D)} - 1`. -/
def degreeEulerFactorFamily (D : FiniteOrbitFrobeniusData)
    (m : PositiveDegreeIndex) : ℚ⟦X⟧ :=
  inverseEulerFactor ℚ (m : ℕ) ^ D.orbitCount (m : ℕ) - 1

/-- `lemma:weil-degree-euler-factor-family-positive`.  Every degree-grouped
Euler factor has constant coefficient zero. -/
theorem degreeEulerFactorFamily_positive (D : FiniteOrbitFrobeniusData)
    (m : PositiveDegreeIndex) :
    constantCoeff (D.degreeEulerFactorFamily m) = 0 := by
  rw [degreeEulerFactorFamily, map_sub, map_one, map_pow,
    inverseEulerFactor_constantCoeff m.2, one_pow, sub_self]

/-- If `N < (m : ℕ)`, then `v_m ≡_N 0`: the inverse Euler factor agrees with
one through `N`, hence so does its `a_m(D)`-th power. -/
theorem degreeEulerFactorFamily_agree_zero (D : FiniteOrbitFrobeniusData)
    {m : PositiveDegreeIndex} {N : ℕ} (hNm : N < (m : ℕ)) :
    PowerSeries.AgreeThrough N (D.degreeEulerFactorFamily m) 0 := by
  have hE : PowerSeries.AgreeThrough N (inverseEulerFactor ℚ (m : ℕ)) 1 := by
    have h := PowerSeries.AgreeThrough.one_add
      (inverseEulerFactorPositivePart_agreeThrough (R := ℚ) hNm)
    rwa [show (1 : ℚ⟦X⟧) + inverseEulerFactorPositivePart ℚ (m : ℕ) =
        inverseEulerFactor ℚ (m : ℕ) by
      rw [inverseEulerFactorPositivePart]; ring] at h
  have hpow := hE.pow (D.orbitCount (m : ℕ))
  rw [one_pow] at hpow
  have hsub := hpow.sub (PowerSeries.AgreeThrough.refl N 1)
  rwa [sub_self] at hsub

/-- `lemma:weil-degree-euler-factor-family-locally-finite`.  For every `N`,
only finitely many positive degrees have `v_m ≢_N 0`. -/
theorem degreeEulerFactorFamily_locallyFinite (D : FiniteOrbitFrobeniusData)
    (N : ℕ) :
    {m : PositiveDegreeIndex |
      ¬ PowerSeries.AgreeThrough N (D.degreeEulerFactorFamily m) 0}.Finite := by
  have hsub : {m : PositiveDegreeIndex |
      ¬ PowerSeries.AgreeThrough N (D.degreeEulerFactorFamily m) 0} ⊆
      Subtype.val ⁻¹' ↑(Finset.Icc 1 N) := by
    intro m hm
    simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc]
    refine ⟨m.2, ?_⟩
    by_contra hNm
    exact hm (D.degreeEulerFactorFamily_agree_zero (by omega))
  exact Set.Finite.subset
    (Set.Finite.preimage Subtype.val_injective.injOn
      (Finset.Icc 1 N).finite_toSet) hsub

/-- `def:weil-degree-euler-locally-finite-family`.  The packaged
degree-grouped Euler family `𝓖_D` indexed by positive degrees, with
component `v_m = E_m^{a_m(D)} - 1`. -/
def degreeEulerFamily (D : FiniteOrbitFrobeniusData) :
    TAdicallyLocallyFiniteFamily ℚ PositiveDegreeIndex where
  toFun := D.degreeEulerFactorFamily
  constantCoeff_eq_zero := D.degreeEulerFactorFamily_positive
  finite_active := D.degreeEulerFactorFamily_locallyFinite

/-- `def:weil-degree-euler-product`.  The degree-grouped Euler product
`Z_{deg,D} = ∏^lf_{m ∈ ℕ_{>0}} E_m^{a_m(D)}`. -/
def degreeEulerProduct (D : FiniteOrbitFrobeniusData) : ℚ⟦X⟧ :=
  D.degreeEulerFamily.product

open scoped Classical in
/-- `lemma:weil-bounded-orbit-degree-fiber`.  A bounded-orbit degree fiber is
the one-degree orbit finset: for `N ≥ 1` and `m ∈ I_N⁺`,
`𝒪_{≤N}.filter (deg_F · = m) = 𝒪_m`. -/
theorem boundedOrbit_degreeFiber (D : FiniteOrbitFrobeniusData) {N : ℕ}
    (hN : 1 ≤ N) {m : PositiveDegreeIndex}
    (hm : m ∈ positiveDegreeIndexFinset N) :
    (D.boundedOrbitFinset N).filter (fun O => Orbit.degree O = (m : ℕ)) =
      D.degreeOrbitFinset (m : ℕ) := by
  ext O
  rw [Finset.mem_filter, D.mem_boundedOrbitFinset hN O,
    D.mem_degreeOrbitFinset m.2 O]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [h]
    exact (mem_positiveDegreeIndexFinset m).mp hm

/-- `lemma:weil-bounded-orbit-product-regroup-by-degree`.  Finite
bounded-orbit products regroup by degree:
`∏_{O ∈ 𝒪_{≤N}} E_{deg_F(O)} = ∏_{m ∈ I_N⁺} E_m^{a_m(D)}`. -/
theorem boundedOrbitProduct_regroup_degree (D : FiniteOrbitFrobeniusData)
    {N : ℕ} (hN : 1 ≤ N) :
    ∏ O ∈ D.boundedOrbitFinset N, inverseEulerFactor ℚ (Orbit.degree O) =
      ∏ m ∈ positiveDegreeIndexFinset N,
        inverseEulerFactor ℚ (m : ℕ) ^ D.orbitCount (m : ℕ) := by
  classical
  have hunion : D.boundedOrbitFinset N =
      (positiveDegreeIndexFinset N).biUnion
        fun m => D.degreeOrbitFinset (m : ℕ) := by
    ext O
    rw [Finset.mem_biUnion, D.mem_boundedOrbitFinset hN O]
    constructor
    · intro hle
      exact ⟨⟨Orbit.degree O, O.degree_pos⟩,
        (mem_positiveDegreeIndexFinset _).mpr hle,
        (D.mem_degreeOrbitFinset O.degree_pos O).mpr rfl⟩
    · rintro ⟨m, hm, hO⟩
      rw [(D.mem_degreeOrbitFinset m.2 O).mp hO]
      exact (mem_positiveDegreeIndexFinset m).mp hm
  have hdisj : (↑(positiveDegreeIndexFinset N) :
      Set PositiveDegreeIndex).PairwiseDisjoint
      fun m => D.degreeOrbitFinset (m : ℕ) := by
    intro m hm m' hm' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro O hO hO'
    apply hne
    apply Subtype.ext
    rw [← (D.mem_degreeOrbitFinset m.2 O).mp hO,
      ← (D.mem_degreeOrbitFinset m'.2 O).mp hO']
  rw [hunion, Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun m _ => ?_
  calc ∏ O ∈ D.degreeOrbitFinset (m : ℕ),
        inverseEulerFactor ℚ (Orbit.degree O)
      = ∏ _O ∈ D.degreeOrbitFinset (m : ℕ), inverseEulerFactor ℚ (m : ℕ) :=
        Finset.prod_congr rfl fun O hO => by
          rw [(D.mem_degreeOrbitFinset m.2 O).mp hO]
    _ = inverseEulerFactor ℚ (m : ℕ) ^ D.orbitCount (m : ℕ) := by
        rw [Finset.prod_const, orbitCount]

/-- `lemma:weil-degree-euler-active-finset-subset`.  Active degree indices
are bounded by the truncation degree: `A_N(𝓖_D) ⊆ I_N⁺`. -/
theorem degreeEulerFamily_activeFinset_subset (D : FiniteOrbitFrobeniusData)
    (N : ℕ) :
    D.degreeEulerFamily.activeFinset N ⊆ positiveDegreeIndexFinset N := by
  intro m hm
  rw [TAdicallyLocallyFiniteFamily.mem_activeFinset] at hm
  rw [mem_positiveDegreeIndexFinset]
  by_contra hNm
  exact hm (D.degreeEulerFactorFamily_agree_zero (by omega))

/-- `lemma:weil-degree-euler-product-agree-bounded-product`.  The degree
Euler product has the bounded-degree truncation:
`Z_{deg,D} ≡_N ∏_{m ∈ I_N⁺} E_m^{a_m(D)}`. -/
theorem degreeEulerProduct_agree_boundedProduct (D : FiniteOrbitFrobeniusData)
    (N : ℕ) :
    PowerSeries.AgreeThrough N D.degreeEulerProduct
      (∏ m ∈ positiveDegreeIndexFinset N,
        inverseEulerFactor ℚ (m : ℕ) ^ D.orbitCount (m : ℕ)) := by
  have h := D.degreeEulerFamily.product_agree_finset
    (D.degreeEulerFamily_activeFinset_subset N)
  have hfac : ∀ m ∈ positiveDegreeIndexFinset N,
      (1 : ℚ⟦X⟧) + D.degreeEulerFamily.toFun m =
        inverseEulerFactor ℚ (m : ℕ) ^ D.orbitCount (m : ℕ) := by
    intro m _
    show (1 : ℚ⟦X⟧) +
      (inverseEulerFactor ℚ (m : ℕ) ^ D.orbitCount (m : ℕ) - 1) = _
    ring
  rw [Finset.prod_congr rfl hfac] at h
  exact h

/-- `lemma:weil-orbit-euler-product-agree-bounded-product`.  The orbit Euler
product has the bounded-orbit truncation: for `N ≥ 1`,
`Z_{orb,D} ≡_N ∏_{O ∈ 𝒪_{≤N}} E_{deg_F(O)}`. -/
theorem orbitEulerProduct_agree_boundedProduct (D : FiniteOrbitFrobeniusData)
    {N : ℕ} (hN : 1 ≤ N) :
    PowerSeries.AgreeThrough N D.orbitEulerProduct
      (∏ O ∈ D.boundedOrbitFinset N,
        inverseEulerFactor ℚ (Orbit.degree O)) := by
  have h := D.orbitEulerFamily.product_agree N
  rw [TAdicallyLocallyFiniteFamily.truncatedProduct,
    D.orbitEulerFamily_activeFinset hN] at h
  have hfac : ∀ O ∈ D.boundedOrbitFinset N,
      (1 : ℚ⟦X⟧) + D.orbitEulerFamily.toFun O =
        inverseEulerFactor ℚ (Orbit.degree O) :=
    fun O _ => D.one_add_orbitEulerFactorFamily O
  rw [Finset.prod_congr rfl hfac] at h
  exact h

/-- `prop:weil-orbit-euler-product-grouped`.  Regrouping the orbit Euler
product by degree: `Z_{orb,D} = Z_{deg,D}`. -/
theorem orbitEulerProduct_eq_degreeEulerProduct (D : FiniteOrbitFrobeniusData) :
    D.orbitEulerProduct = D.degreeEulerProduct := by
  ext N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [coeff_zero_eq_constantCoeff_apply]
    rw [D.orbitEulerProduct_constantCoeff, degreeEulerProduct,
      TAdicallyLocallyFiniteFamily.product_constantCoeff]
  · rw [D.orbitEulerProduct_agree_boundedProduct hN N le_rfl,
      D.degreeEulerProduct_agree_boundedProduct N N le_rfl,
      D.boundedOrbitProduct_regroup_degree hN]

/-- `cor:weil-orbit-zeta-three-forms`.  Three equivalent forms of the orbit
zeta series in `ℚ⟦T⟧`:
`Z_{cnt,D} = Exp(S_D) = ∏^lf_O E_{deg_F(O)} = ∏^lf_{m ∈ ℕ_{>0}} E_m^{a_m(D)}`,
together with `c(Z_{cnt,D}) = 1` and the integer-coefficient predicate
inside `ℚ⟦T⟧` (no typed lift into `ℤ⟦T⟧` is asserted). -/
theorem zeta_three_forms (D : FiniteOrbitFrobeniusData) :
    D.countingZetaSeries = formalExp D.countingLogSeries ∧
      D.countingZetaSeries = D.orbitEulerProduct ∧
        D.countingZetaSeries = D.degreeEulerProduct ∧
          constantCoeff D.countingZetaSeries = 1 ∧
            PowerSeries.HasCoefficientsIn D.countingZetaSeries
              (algebraMap ℤ ℚ).range :=
  ⟨rfl, D.orbitEulerProduct_eq_countingZeta,
    D.orbitEulerProduct_eq_countingZeta.trans
      D.orbitEulerProduct_eq_degreeEulerProduct,
    formalExp_constantCoeff D.countingLogSeries_positive,
    D.countingZetaSeries_integral⟩

end FiniteOrbitFrobeniusData

end

end Weil
