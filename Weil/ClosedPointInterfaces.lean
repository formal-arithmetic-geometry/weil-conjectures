/-
Formalization of Chapter 3, Section 6 of `weil_conjectures_chapter3.tex`:
"Abstract finite-extension and closed-point interfaces"
(`sec:weil-closed-point-interface`).

Every declaration below is annotated with the LaTeX label it formalizes.
Design notes, following the conventions of the earlier section files:

* The two interface structures package explicit combinatorial assumptions;
  no construction of them from schemes is asserted, exactly as in the text.
* Per the "Rational coefficient scope" paragraph of the previous section,
  the coefficient ring stays literally `ℚ`.
* The universe of the point types (`Rat`, `ClosedPoint`) is a fresh
  parameter, independent of the universe of `D.points`; the comparison
  data are `Equiv`s, which are universe-heterogeneous.
* `ratFintype` is a plain structure field (the "selected instance" of the
  text); it is installed with `letI` exactly where the text installs it.
* The subtype `{x : Ω | x ∈ Fix_D(n)}` of the text is
  `{x : D.points // x ∈ D.fixedPointFinset n}`, definitionally the
  coercion to a type of the finset `Fix_D(n)`, so the cardinal comparisons
  go through `Fintype.card_coe` as prescribed.
-/
import Weil.OrbitEulerProducts

open PowerSeries

namespace Weil

noncomputable section

universe u v

/-! ### The finite-extension point interface -/

/-- `def:weil-finite-extension-point-interface`.  A finite-extension point
interface over a finite-orbit datum `D`: a family of finite types
`Rat n` of `n`-th extension points together with, for every positive `n`, a
selected comparison equivalence with the fixed-point finset `Fix_D(n)`.
The type and its selected finite structure do not depend on a positivity
proof; only the comparison equivalence takes one. -/
structure FiniteExtensionPointInterface (D : FiniteOrbitFrobeniusData.{u}) where
  Rat : ℕ → Type v
  ratFintype : ∀ n, Fintype (Rat n)
  rho : ∀ (n : ℕ), 0 < n →
    Rat n ≃ {x : D.points // x ∈ D.fixedPointFinset n}

namespace FiniteExtensionPointInterface

variable {D : FiniteOrbitFrobeniusData}

/-- `def:weil-finite-extension-point-count`.  The finite-extension point
count `N_n(P) = Fintype.card (Rat_P n)`, taken with the selected instance
`P.ratFintype n`. -/
def pointCount (P : FiniteExtensionPointInterface D) (n : ℕ) : ℕ :=
  letI := P.ratFintype n
  Fintype.card (P.Rat n)

/-- `lemma:weil-finite-extension-point-count-eq-fixed`.  The
finite-extension point count equals the fixed-point count: `N_n(P) = N_n(D)`
for `n ≥ 1`. -/
theorem pointCount_eq_fixedPointCount (P : FiniteExtensionPointInterface D)
    {n : ℕ} (hn : 1 ≤ n) :
    P.pointCount n = D.fixedPointCount n := by
  rw [pointCount, FiniteOrbitFrobeniusData.fixedPointCount,
    ← Fintype.card_coe]
  exact @Fintype.card_congr _ _ (P.ratFintype n) _ (P.rho n hn)

/-- `def:weil-finite-extension-counting-log-series`.  The finite-extension
counting logarithm `S_P ∈ ℚ⟦T⟧` with `[T^0]S_P = 0` and
`[T^n]S_P = N_n(P)/n` for `n ≥ 1`. -/
def countingLogSeries (P : FiniteExtensionPointInterface D) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else (P.pointCount n : ℚ) / (n : ℚ)

/-- Coefficient formula of
`def:weil-finite-extension-counting-log-series`, restated through
`PowerSeries.coeff_mk` for rewriting. -/
theorem coeff_countingLogSeries (P : FiniteExtensionPointInterface D)
    (n : ℕ) :
    coeff n P.countingLogSeries =
      if n = 0 then 0 else (P.pointCount n : ℚ) / (n : ℚ) := by
  rw [countingLogSeries, coeff_mk]

/-- `lemma:weil-finite-extension-counting-log-series-positive`.  The
finite-extension counting logarithm has positive order. -/
theorem countingLogSeries_positive (P : FiniteExtensionPointInterface D) :
    constantCoeff P.countingLogSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_countingLogSeries,
    if_pos rfl]

/-- `def:weil-bundled-finite-extension-counting-log-series`.  The bundled
finite-extension counting logarithm `S_P⁺ ∈ PositiveSeries(ℚ)`. -/
def positiveCountingLogSeries (P : FiniteExtensionPointInterface D) :
    PositiveSeries ℚ :=
  ⟨P.countingLogSeries, P.countingLogSeries_positive⟩

/-- `def:weil-finite-extension-counting-zeta-series`.  The finite-extension
counting zeta series `Z_P = Exp(S_P)`; the customary
`Exp(∑_{n≥1} N_n(P)Tⁿ/n)` is only coefficientwise shorthand. -/
def countingZetaSeries (P : FiniteExtensionPointInterface D) : ℚ⟦X⟧ :=
  formalExp P.countingLogSeries

/-- `prop:weil-finite-extension-zeta-eq-orbit-zeta`.  The finite-extension
and orbit counting zeta series agree: `Z_P = Z_{cnt,D}`. -/
theorem countingZetaSeries_eq (P : FiniteExtensionPointInterface D) :
    P.countingZetaSeries = D.countingZetaSeries := by
  have hS : P.countingLogSeries = D.countingLogSeries := by
    ext n
    rw [coeff_countingLogSeries,
      FiniteOrbitFrobeniusData.coeff_countingLogSeries]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = 0),
        P.pointCount_eq_fixedPointCount hn]
  rw [countingZetaSeries, FiniteOrbitFrobeniusData.countingZetaSeries, hS]

end FiniteExtensionPointInterface

/-! ### The closed-point–orbit interface -/

/-- `def:weil-closed-point-orbit-interface`.  A closed-point–orbit interface
over `D`: a type of closed points with a degree function bounded below by
one, a selected equivalence `θ_C` with the type of Frobenius orbits, and the
degree compatibility `deg_C(c) = deg_F(θ_C(c))`. -/
structure ClosedPointOrbitInterface (D : FiniteOrbitFrobeniusData.{u}) where
  ClosedPoint : Type v
  degree : ClosedPoint → ℕ
  one_le_degree : ∀ c, 1 ≤ degree c
  theta : ClosedPoint ≃ D.Orbit
  degree_eq : ∀ c,
    degree c = FiniteOrbitFrobeniusData.Orbit.degree (theta c)

namespace ClosedPointOrbitInterface

open FiniteOrbitFrobeniusData

variable {D : FiniteOrbitFrobeniusData}

/-- `def:weil-degree-closed-point-finset`.  The finset `𝒞_m` of closed
points of one degree `m`, the `Finset.preimage` of the one-degree orbit
finset `𝒪_m` under `θ_C`. -/
def degreeClosedPointFinset (C : ClosedPointOrbitInterface D) (m : ℕ) :
    Finset C.ClosedPoint :=
  (D.degreeOrbitFinset m).preimage C.theta C.theta.injective.injOn

/-- `lemma:weil-degree-closed-point-finset-mem`.  Membership in the
one-degree closed-point finset at positive degrees. -/
theorem mem_degreeClosedPointFinset (C : ClosedPointOrbitInterface D)
    {m : ℕ} (hm : 1 ≤ m) (c : C.ClosedPoint) :
    c ∈ C.degreeClosedPointFinset m ↔ C.degree c = m := by
  rw [degreeClosedPointFinset, Finset.mem_preimage,
    D.mem_degreeOrbitFinset hm (C.theta c), ← C.degree_eq c]

/-- `def:weil-closed-point-count`.  The number `b_m(C) = #𝒞_m` of closed
points of one degree. -/
def closedPointCount (C : ClosedPointOrbitInterface D) (m : ℕ) : ℕ :=
  (C.degreeClosedPointFinset m).card

/-- `def:weil-degree-closed-point-forward-candidate`.  The forward candidate
`f_m(c) = θ_C(c.1)` on a fixed closed-point degree. -/
def degreeForwardCandidate (C : ClosedPointOrbitInterface D) (m : ℕ)
    (c : {c : C.ClosedPoint // c ∈ C.degreeClosedPointFinset m}) : D.Orbit :=
  C.theta c.1

/-- `lemma:weil-degree-closed-point-forward-candidate-mem`.  The fixed-degree
forward candidate lands in the orbit fiber. -/
theorem degreeForwardCandidate_mem (C : ClosedPointOrbitInterface D) (m : ℕ)
    (c : {c : C.ClosedPoint // c ∈ C.degreeClosedPointFinset m}) :
    C.degreeForwardCandidate m c ∈ D.degreeOrbitFinset m := by
  have h : c.1 ∈ (D.degreeOrbitFinset m).preimage C.theta
      C.theta.injective.injOn := c.2
  have h2 := Finset.mem_preimage.mp h
  exact h2

/-- `def:weil-degree-closed-point-forward-map`.  The forward map `f̄_m` on a
fixed closed-point degree, pairing the forward candidate with its fiber
membership. -/
def degreeForwardMap (C : ClosedPointOrbitInterface D) (m : ℕ)
    (c : {c : C.ClosedPoint // c ∈ C.degreeClosedPointFinset m}) :
    {O : D.Orbit // O ∈ D.degreeOrbitFinset m} :=
  ⟨C.degreeForwardCandidate m c, C.degreeForwardCandidate_mem m c⟩

/-- `def:weil-degree-closed-point-inverse-candidate`.  The inverse candidate
`g_m(O) = θ_C⁻¹(O.1)` on a fixed orbit degree. -/
def degreeInverseCandidate (C : ClosedPointOrbitInterface D) (m : ℕ)
    (O : {O : D.Orbit // O ∈ D.degreeOrbitFinset m}) : C.ClosedPoint :=
  C.theta.symm O.1

/-- `lemma:weil-degree-closed-point-inverse-candidate-mem`.  The fixed-degree
inverse candidate lands in the closed-point fiber. -/
theorem degreeInverseCandidate_mem (C : ClosedPointOrbitInterface D) (m : ℕ)
    (O : {O : D.Orbit // O ∈ D.degreeOrbitFinset m}) :
    C.degreeInverseCandidate m O ∈ C.degreeClosedPointFinset m := by
  refine Finset.mem_preimage.mpr ?_
  show C.theta (C.theta.symm O.1) ∈ D.degreeOrbitFinset m
  rw [C.theta.apply_symm_apply]
  exact O.2

/-- `def:weil-degree-closed-point-inverse-map`.  The inverse map `ḡ_m` on a
fixed orbit degree, pairing the inverse candidate with its fiber
membership. -/
def degreeInverseMap (C : ClosedPointOrbitInterface D) (m : ℕ)
    (O : {O : D.Orbit // O ∈ D.degreeOrbitFinset m}) :
    {c : C.ClosedPoint // c ∈ C.degreeClosedPointFinset m} :=
  ⟨C.degreeInverseCandidate m O, C.degreeInverseCandidate_mem m O⟩

/-- `lemma:weil-degree-closed-point-maps-left-inverse`.  The inverse map is
a left inverse of the forward map. -/
theorem degreeMaps_leftInverse (C : ClosedPointOrbitInterface D) (m : ℕ)
    (c : {c : C.ClosedPoint // c ∈ C.degreeClosedPointFinset m}) :
    C.degreeInverseMap m (C.degreeForwardMap m c) = c := by
  apply Subtype.ext
  show C.theta.symm (C.theta c.1) = c.1
  exact C.theta.symm_apply_apply c.1

/-- `lemma:weil-degree-closed-point-maps-right-inverse`.  The inverse map is
a right inverse of the forward map. -/
theorem degreeMaps_rightInverse (C : ClosedPointOrbitInterface D) (m : ℕ)
    (O : {O : D.Orbit // O ∈ D.degreeOrbitFinset m}) :
    C.degreeForwardMap m (C.degreeInverseMap m O) = O := by
  apply Subtype.ext
  show C.theta (C.theta.symm O.1) = O.1
  exact C.theta.apply_symm_apply O.1

/-- `def:weil-degree-closed-point-orbit-equiv`.  The equivalence `θ̄_{C,m}`
of fixed-degree closed points and orbits, assembled from the forward and
inverse maps and the two inverse laws. -/
def degreeEquiv (C : ClosedPointOrbitInterface D) (m : ℕ) :
    {c : C.ClosedPoint // c ∈ C.degreeClosedPointFinset m} ≃
      {O : D.Orbit // O ∈ D.degreeOrbitFinset m} where
  toFun := C.degreeForwardMap m
  invFun := C.degreeInverseMap m
  left_inv := C.degreeMaps_leftInverse m
  right_inv := C.degreeMaps_rightInverse m

/-- `lemma:weil-closed-point-count-eq-orbit-count`.  Closed-point degree
counts equal orbit degree counts: `b_m(C) = a_m(D)` for `m ≥ 1`. -/
theorem closedPointCount_eq_orbitCount (C : ClosedPointOrbitInterface D)
    {m : ℕ} (_hm : 1 ≤ m) :
    C.closedPointCount m = D.orbitCount m := by
  rw [closedPointCount, FiniteOrbitFrobeniusData.orbitCount,
    ← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (C.degreeEquiv m)

/-! ### The closed-point Euler product -/

/-- `def:weil-closed-point-euler-factor-family`.  The raw closed-point
Euler-factor family `w_c = E_{deg_C(c)} - 1 ∈ ℚ⟦T⟧`. -/
def eulerFactorFamily (C : ClosedPointOrbitInterface D) (c : C.ClosedPoint) :
    ℚ⟦X⟧ :=
  inverseEulerFactorPositivePart ℚ (C.degree c)

/-- `lemma:weil-closed-point-euler-factor-family-positive`.  Every
closed-point Euler factor has constant coefficient zero. -/
theorem eulerFactorFamily_positive (C : ClosedPointOrbitInterface D)
    (c : C.ClosedPoint) :
    constantCoeff (C.eulerFactorFamily c) = 0 :=
  inverseEulerFactorPositivePart_constantCoeff (C.degree c)

/-- `lemma:weil-closed-point-euler-component-transport`.  Closed-point
components transport to orbit components: `u_{θ_C(c)} = w_c`. -/
theorem eulerFactorFamily_component_transport (C : ClosedPointOrbitInterface D)
    (c : C.ClosedPoint) :
    D.orbitEulerFactorFamily (C.theta c) = C.eulerFactorFamily c := by
  rw [FiniteOrbitFrobeniusData.orbitEulerFactorFamily, eulerFactorFamily,
    ← C.degree_eq c]

/-- `lemma:weil-closed-point-active-image-subset`.  Active closed points map
into active orbits. -/
theorem activeClosed_image_subset_activeOrbit (C : ClosedPointOrbitInterface D)
    (N : ℕ) :
    C.theta ''
        {c | ¬ PowerSeries.AgreeThrough N (C.eulerFactorFamily c) 0} ⊆
      {O | ¬ PowerSeries.AgreeThrough N (D.orbitEulerFactorFamily O) 0} := by
  rintro O ⟨c, hc, rfl⟩
  show ¬ PowerSeries.AgreeThrough N (D.orbitEulerFactorFamily (C.theta c)) 0
  rw [C.eulerFactorFamily_component_transport c]
  exact hc

/-- `lemma:weil-closed-point-active-image-finite`.  The active closed-point
image is finite. -/
theorem activeClosed_image_finite (C : ClosedPointOrbitInterface D) (N : ℕ) :
    (C.theta ''
      {c | ¬ PowerSeries.AgreeThrough N (C.eulerFactorFamily c) 0}).Finite :=
  Set.Finite.subset (D.orbitEulerFactorFamily_locallyFinite N)
    (C.activeClosed_image_subset_activeOrbit N)

/-- `lemma:weil-closed-point-euler-factor-family-locally-finite`.  For every
`N`, only finitely many closed points have `w_c ≢_N 0`. -/
theorem eulerFactorFamily_locallyFinite (C : ClosedPointOrbitInterface D)
    (N : ℕ) :
    {c : C.ClosedPoint |
      ¬ PowerSeries.AgreeThrough N (C.eulerFactorFamily c) 0}.Finite :=
  Set.Finite.of_finite_image (C.activeClosed_image_finite N)
    C.theta.injective.injOn

/-- `def:weil-closed-point-euler-locally-finite-family`.  The packaged
closed-point Euler family `𝓔_C` indexed by closed points, with component
`w_c`. -/
def eulerFamily (C : ClosedPointOrbitInterface D) :
    TAdicallyLocallyFiniteFamily ℚ C.ClosedPoint where
  toFun := C.eulerFactorFamily
  constantCoeff_eq_zero := C.eulerFactorFamily_positive
  finite_active := C.eulerFactorFamily_locallyFinite

/-- `def:weil-closed-point-euler-product`.  The closed-point Euler product
`Z_{cl,C} = ∏^lf_{c} E_{deg_C(c)}`. -/
def eulerProduct (C : ClosedPointOrbitInterface D) : ℚ⟦X⟧ :=
  C.eulerFamily.product

/-- `lemma:weil-closed-point-active-iff-orbit-active`.  Active closed points
correspond exactly to active orbits: `c ∈ A_N(𝓔_C) ↔ θ_C(c) ∈ A_N(𝓔_D)`. -/
theorem mem_activeFinset_iff (C : ClosedPointOrbitInterface D) (N : ℕ)
    (c : C.ClosedPoint) :
    c ∈ C.eulerFamily.activeFinset N ↔
      C.theta c ∈ D.orbitEulerFamily.activeFinset N := by
  rw [TAdicallyLocallyFiniteFamily.mem_activeFinset,
    TAdicallyLocallyFiniteFamily.mem_activeFinset]
  show ¬ PowerSeries.AgreeThrough N (C.eulerFactorFamily c) 0 ↔
    ¬ PowerSeries.AgreeThrough N (D.orbitEulerFactorFamily (C.theta c)) 0
  rw [C.eulerFactorFamily_component_transport c]

/-- `lemma:weil-closed-point-truncated-product-reindex`.  Closed-point and
orbit truncated products agree: `Π_N(𝓔_C) = Π_N(𝓔_D)`. -/
theorem truncatedProduct_eq (C : ClosedPointOrbitInterface D) (N : ℕ) :
    C.eulerFamily.truncatedProduct N =
      D.orbitEulerFamily.truncatedProduct N := by
  rw [TAdicallyLocallyFiniteFamily.truncatedProduct,
    TAdicallyLocallyFiniteFamily.truncatedProduct]
  refine Finset.prod_equiv C.theta (fun c => C.mem_activeFinset_iff N c)
    fun c _ => ?_
  show 1 + C.eulerFactorFamily c =
    1 + D.orbitEulerFactorFamily (C.theta c)
  rw [C.eulerFactorFamily_component_transport c]

/-- `lemma:weil-closed-point-euler-product-coeff-reindex`.  Closed-point and
orbit Euler products agree coefficientwise. -/
theorem coeff_eulerProduct_eq (C : ClosedPointOrbitInterface D) (N : ℕ) :
    coeff N C.eulerProduct = coeff N D.orbitEulerProduct := by
  rw [eulerProduct, FiniteOrbitFrobeniusData.orbitEulerProduct,
    C.eulerFamily.coeff_product, D.orbitEulerFamily.coeff_product,
    C.truncatedProduct_eq N]

/-- `prop:weil-closed-point-euler-product-reindex`.  Reindexing the
closed-point product by Frobenius orbits: `Z_{cl,C} = Z_{orb,D}`. -/
theorem eulerProduct_eq_orbitEulerProduct (C : ClosedPointOrbitInterface D) :
    C.eulerProduct = D.orbitEulerProduct := by
  ext N
  exact C.coeff_eulerProduct_eq N

/-- `thm:weil-closed-point-euler-exponential`.  Given both interfaces over
the same datum: `Z_P = Z_{cl,C} = ∏^lf_c E_{deg_C(c)}` (the product being
`def:weil-closed-point-euler-product`), with `c(Z_P) = 1` and integer
coefficients inside `ℚ⟦T⟧`; no typed object of `ℤ⟦T⟧` is asserted. -/
theorem eulerProduct_eq_countingZeta (C : ClosedPointOrbitInterface D)
    (P : FiniteExtensionPointInterface D) :
    P.countingZetaSeries = C.eulerProduct ∧
      constantCoeff P.countingZetaSeries = 1 ∧
        PowerSeries.HasCoefficientsIn P.countingZetaSeries
          (algebraMap ℤ ℚ).range := by
  have h1 : P.countingZetaSeries = C.eulerProduct := by
    rw [P.countingZetaSeries_eq, D.orbitEulerProduct_eq_countingZeta,
      C.eulerProduct_eq_orbitEulerProduct]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, C.eulerProduct_eq_orbitEulerProduct]
    exact D.orbitEulerProduct_constantCoeff
  · rw [P.countingZetaSeries_eq]
    exact D.countingZetaSeries_integral

/-- `lemma:weil-positive-divisor-quotient-positive`.  A quotient by a
positive divisor is positive; the hypothesis `0 < m` is retained from the
text although the divisor-membership lemmas do not need it. -/
theorem _root_.Weil.natDiv_pos_of_mem_divisors {m r : ℕ} (_hm : 0 < m)
    (hr : r ∈ m.divisors) : 0 < m / r :=
  Nat.div_pos (Nat.divisor_le hr) (Nat.pos_of_mem_divisors hr)

/-- `cor:weil-closed-point-mobius-recovery`.  Closed points recovered from
finite-extension point counts:
`b_m(C) = (1/m) ∑_{r ∣ m} μ(r) N_{m/r}(P)` in `ℚ` for `m ≥ 1`. -/
theorem closedPointCount_eq_mobius (C : ClosedPointOrbitInterface D)
    (P : FiniteExtensionPointInterface D) {m : ℕ} (hm : 1 ≤ m) :
    (C.closedPointCount m : ℚ) =
      1 / (m : ℚ) *
        ∑ r ∈ m.divisors,
          (ArithmeticFunction.moebius r : ℚ) *
            (P.pointCount (m / r) : ℚ) := by
  rw [C.closedPointCount_eq_orbitCount hm, D.orbitCount_eq_mobius hm]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [P.pointCount_eq_fixedPointCount
    (Weil.natDiv_pos_of_mem_divisors (by omega) hr)]

end ClosedPointOrbitInterface

end

end Weil
