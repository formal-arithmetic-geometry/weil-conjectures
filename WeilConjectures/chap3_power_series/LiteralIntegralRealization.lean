/-
Formalization of Chapter 3, Section 8 of `weil_conjectures_chapter3.tex`:
"Literal integral power-series realization"
(`sec:weil-literal-integral-realization-promoted`).

Every declaration below is annotated with the LaTeX label it formalizes.
Design notes, following the conventions of the earlier section files:

* Every coefficient-ring comparison uses only the forward ring homomorphism
  `ι_* = PowerSeries.map (algebraMap ℤ ℚ)`; no map in the reverse direction
  and no coefficientwise choice of integral preimages occurs, exactly as in
  the text.
* The generic integral-family subchain (`rationalComponents` through
  `product_rationalization`) is stated for an arbitrary
  `TAdicallyLocallyFiniteFamily ℤ I`, then specialized to the three
  integral families of `Weil.IntegralEulerFamilies`.
* The component-projection lemmas
  (`integerOrbitEulerFamily_component`, ...) are the definitional
  reflexivities demanded by the text; they are recorded so that later
  rewriting steps can cite them by name.
-/
module

public import WeilConjectures.chap3_power_series.IntegralEulerFamilies

@[expose] public section

open PowerSeries

namespace Weil

noncomputable section

/-! ### The integer-to-rational scalar extension -/

/-- `def:weil-power-series-integer-to-rational`.  The ring homomorphism
`ι_* : ℤ⟦T⟧ →+* ℚ⟦T⟧`, coefficientwise application of `algebraMap ℤ ℚ`. -/
def powerSeriesIntegerToRational : ℤ⟦X⟧ →+* ℚ⟦X⟧ :=
  PowerSeries.map (algebraMap ℤ ℚ)

/-- `lemma:weil-power-series-integer-to-rational-coeff`.  Coefficient
formula for the integer-to-rational scalar extension. -/
theorem powerSeriesIntegerToRational_coeff (A : ℤ⟦X⟧) (n : ℕ) :
    coeff n (powerSeriesIntegerToRational A) = algebraMap ℤ ℚ (coeff n A) := by
  rw [powerSeriesIntegerToRational, coeff_map]

/-- `lemma:weil-power-series-integer-to-rational-injective`.  The
integer-to-rational scalar extension is injective. -/
theorem powerSeriesIntegerToRational_injective :
    Function.Injective powerSeriesIntegerToRational := by
  intro A B h
  ext n
  have hc : coeff n (powerSeriesIntegerToRational A) =
      coeff n (powerSeriesIntegerToRational B) := by rw [h]
  rw [powerSeriesIntegerToRational_coeff, powerSeriesIntegerToRational_coeff]
    at hc
  exact RingHom.injective_int (algebraMap ℤ ℚ) hc

/-! ### Rationalization of an integral locally finite family -/

namespace TAdicallyLocallyFiniteFamily

variable {I : Type*}

/-- `def:weil-integer-family-rational-components`.  The raw rational
component family `u_i^ℚ = ι_*(u_i)` of an integral locally finite
family. -/
def rationalComponents (u : TAdicallyLocallyFiniteFamily ℤ I) (i : I) :
    ℚ⟦X⟧ :=
  powerSeriesIntegerToRational (u.toFun i)

/-- `lemma:weil-power-series-integer-to-rational-agree-through`.  Scalar
extension reflects finite-degree agreement:
`A ≡_N B ↔ ι_*(A) ≡_N ι_*(B)`. -/
theorem _root_.Weil.powerSeriesIntegerToRational_agreeThrough
    (A B : ℤ⟦X⟧) (N : ℕ) :
    PowerSeries.AgreeThrough N A B ↔
      PowerSeries.AgreeThrough N (powerSeriesIntegerToRational A)
        (powerSeriesIntegerToRational B) := by
  constructor
  · intro h j hj
    rw [powerSeriesIntegerToRational_coeff, powerSeriesIntegerToRational_coeff,
      h j hj]
  · intro h j hj
    have hc := h j hj
    rw [powerSeriesIntegerToRational_coeff, powerSeriesIntegerToRational_coeff]
      at hc
    exact RingHom.injective_int (algebraMap ℤ ℚ) hc

/-- `lemma:weil-integer-family-rational-components-coeff`.  Coefficient
formula for a mapped component. -/
theorem coeff_rationalComponents (u : TAdicallyLocallyFiniteFamily ℤ I)
    (i : I) (n : ℕ) :
    coeff n (u.rationalComponents i) = algebraMap ℤ ℚ (coeff n (u.toFun i)) := by
  rw [rationalComponents, powerSeriesIntegerToRational_coeff]

/-- `lemma:weil-integer-family-rational-components-positive`.  Mapped
components retain positive order. -/
theorem rationalComponents_positive (u : TAdicallyLocallyFiniteFamily ℤ I)
    (i : I) :
    constantCoeff (u.rationalComponents i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, u.coeff_rationalComponents,
    coeff_zero_eq_constantCoeff_apply, u.constantCoeff_eq_zero, map_zero]

/-- `lemma:weil-integer-family-rational-components-active-iff`.  Activity is
preserved by integer-to-rational scalar extension. -/
theorem rationalComponents_active_iff (u : TAdicallyLocallyFiniteFamily ℤ I)
    (i : I) (N : ℕ) :
    ¬ PowerSeries.AgreeThrough N (u.toFun i) 0 ↔
      ¬ PowerSeries.AgreeThrough N (u.rationalComponents i) 0 := by
  apply not_congr
  have h := Weil.powerSeriesIntegerToRational_agreeThrough (u.toFun i) 0 N
  rwa [map_zero] at h

/-- `lemma:weil-integer-family-rational-components-active-set`.  Equality of
active index sets before and after scalar extension. -/
theorem rationalComponents_activeSet (u : TAdicallyLocallyFiniteFamily ℤ I)
    (N : ℕ) :
    {i : I | ¬ PowerSeries.AgreeThrough N (u.toFun i) 0} =
      {i : I | ¬ PowerSeries.AgreeThrough N (u.rationalComponents i) 0} :=
  Set.ext fun i => u.rationalComponents_active_iff i N

/-- `lemma:weil-integer-family-rational-components-locally-finite`.  Local
finiteness after integer-to-rational scalar extension. -/
theorem rationalComponents_locallyFinite (u : TAdicallyLocallyFiniteFamily ℤ I)
    (N : ℕ) :
    {i : I | ¬ PowerSeries.AgreeThrough N (u.rationalComponents i) 0}.Finite := by
  rw [← u.rationalComponents_activeSet N]
  exact u.finite_active N

/-- `def:weil-integer-family-rational-locally-finite-family`.  The packaged
rational image `u^ℚ` of an integral locally finite family. -/
def rationalization (u : TAdicallyLocallyFiniteFamily ℤ I) :
    TAdicallyLocallyFiniteFamily ℚ I where
  toFun := u.rationalComponents
  constantCoeff_eq_zero := u.rationalComponents_positive
  finite_active := u.rationalComponents_locallyFinite

/-- `lemma:weil-integer-family-rational-active-finset`.  Active-finset
equality after scalar extension: `A_N(u) = A_N(u^ℚ)`. -/
theorem activeFinset_rationalization (u : TAdicallyLocallyFiniteFamily ℤ I)
    (N : ℕ) :
    u.activeFinset N = u.rationalization.activeFinset N := by
  ext i
  rw [mem_activeFinset, mem_activeFinset]
  exact u.rationalComponents_active_iff i N

end TAdicallyLocallyFiniteFamily

/-- `lemma:weil-power-series-integer-to-rational-finset-product`.  Scalar
extension of a finite power-series product. -/
theorem powerSeriesIntegerToRational_finsetProduct {I : Type*} (S : Finset I)
    (A : I → ℤ⟦X⟧) :
    powerSeriesIntegerToRational (∏ i ∈ S, A i) =
      ∏ i ∈ S, powerSeriesIntegerToRational (A i) :=
  map_prod powerSeriesIntegerToRational A S

/-- `lemma:weil-inverse-euler-factor-integer-to-rational`.  Scalar extension
of an integral inverse Euler factor: `ι_*(E_m^ℤ) = E_m^ℚ`. -/
theorem powerSeriesIntegerToRational_inverseEulerFactor {m : ℕ}
    (_hm : 1 ≤ m) :
    powerSeriesIntegerToRational (integralInverseEulerFactor m) =
      inverseEulerFactor ℚ m := by
  rw [powerSeriesIntegerToRational, inverseEulerFactor, algebraMap_int_eq]

/-- `lemma:weil-inverse-euler-positive-part-integer-to-rational`.  Scalar
extension of the positive Euler part: `ι_*(E_m^ℤ - 1) = E_m^ℚ - 1`. -/
theorem powerSeriesIntegerToRational_inverseEulerFactorPositivePart {m : ℕ}
    (hm : 1 ≤ m) :
    powerSeriesIntegerToRational (integralInverseEulerFactor m - 1) =
      inverseEulerFactor ℚ m - 1 := by
  rw [map_sub, map_one, powerSeriesIntegerToRational_inverseEulerFactor hm]

/-! ### Rational realization of the three integral families -/

namespace FiniteOrbitFrobeniusData

/-- `lemma:weil-integer-orbit-euler-family-component`.  The `O`-component of
`𝓔_D^ℤ` is `u_O^ℤ`; definitional reflexivity of the record projection. -/
theorem integerOrbitEulerFamily_component (D : FiniteOrbitFrobeniusData)
    (O : D.Orbit) :
    D.integerOrbitEulerFamily.toFun O = D.integerOrbitEulerFactorFamily O :=
  rfl

/-- `lemma:weil-integer-orbit-euler-family-rational-component`.  The
`O`-component of the rationalization `(𝓔_D^ℤ)^ℚ` is the rational component
`u_O`. -/
theorem integerOrbitEulerFamily_rationalComponent
    (D : FiniteOrbitFrobeniusData) (O : D.Orbit) :
    D.integerOrbitEulerFamily.rationalComponents O =
      D.orbitEulerFactorFamily O := by
  show powerSeriesIntegerToRational (D.integerOrbitEulerFactorFamily O) =
    D.orbitEulerFactorFamily O
  rw [integerOrbitEulerFactorFamily, orbitEulerFactorFamily,
    inverseEulerFactorPositivePart]
  exact powerSeriesIntegerToRational_inverseEulerFactorPositivePart
    O.degree_pos

/-- `lemma:weil-integer-degree-euler-family-component`.  The `m`-component
of `𝓖_D^ℤ` is `v_m^ℤ`; definitional reflexivity of the record
projection. -/
theorem integerDegreeEulerFamily_component (D : FiniteOrbitFrobeniusData)
    (m : PositiveDegreeIndex) :
    D.integerDegreeEulerFamily.toFun m = D.integerDegreeEulerFactorFamily m :=
  rfl

/-- `lemma:weil-integer-degree-euler-family-rational-component`.  The
`m`-component of `(𝓖_D^ℤ)^ℚ` is the rational component `v_m`. -/
theorem integerDegreeEulerFamily_rationalComponent
    (D : FiniteOrbitFrobeniusData) (m : PositiveDegreeIndex) :
    D.integerDegreeEulerFamily.rationalComponents m =
      D.degreeEulerFactorFamily m := by
  show powerSeriesIntegerToRational (D.integerDegreeEulerFactorFamily m) =
    D.degreeEulerFactorFamily m
  rw [integerDegreeEulerFactorFamily, degreeEulerFactorFamily, map_sub,
    map_one, map_pow, powerSeriesIntegerToRational_inverseEulerFactor m.2]

end FiniteOrbitFrobeniusData

namespace ClosedPointOrbitInterface

variable {D : FiniteOrbitFrobeniusData}

/-- `lemma:weil-integer-closed-point-euler-family-component`.  The
`c`-component of `𝓔_C^ℤ` is `w_c^ℤ`; definitional reflexivity of the
record projection. -/
theorem integerEulerFamily_component (C : ClosedPointOrbitInterface D)
    (c : C.ClosedPoint) :
    C.integerEulerFamily.toFun c = C.integerEulerFactorFamily c :=
  rfl

/-- `lemma:weil-integer-closed-point-euler-family-rational-component`.  The
`c`-component of `(𝓔_C^ℤ)^ℚ` is the rational component `w_c`. -/
theorem integerEulerFamily_rationalComponent (C : ClosedPointOrbitInterface D)
    (c : C.ClosedPoint) :
    C.integerEulerFamily.rationalComponents c = C.eulerFactorFamily c := by
  show powerSeriesIntegerToRational (C.integerEulerFactorFamily c) =
    C.eulerFactorFamily c
  rw [integerEulerFactorFamily, eulerFactorFamily,
    inverseEulerFactorPositivePart]
  exact powerSeriesIntegerToRational_inverseEulerFactorPositivePart
    (C.one_le_degree c)

end ClosedPointOrbitInterface

/-! ### Scalar extension of locally finite products -/

/-- `lemma:weil-power-series-integer-to-rational-locally-finite-product`.
Scalar extension of a locally finite product:
`ι_*(∏^lf (1 + u_i)) = ∏^lf (1 + u_i^ℚ)`. -/
theorem TAdicallyLocallyFiniteFamily.product_rationalization {I : Type*}
    (u : TAdicallyLocallyFiniteFamily ℤ I) :
    powerSeriesIntegerToRational u.product = u.rationalization.product := by
  have htrunc : ∀ N : ℕ,
      powerSeriesIntegerToRational (u.truncatedProduct N) =
        u.rationalization.truncatedProduct N := by
    intro N
    rw [truncatedProduct, truncatedProduct, map_prod,
      ← u.activeFinset_rationalization N]
    refine Finset.prod_congr rfl fun i _ => ?_
    show powerSeriesIntegerToRational (1 + u.toFun i) =
      1 + u.rationalComponents i
    rw [map_add, map_one, rationalComponents]
  ext N
  rw [powerSeriesIntegerToRational_coeff, u.coeff_product,
    u.rationalization.coeff_product, ← powerSeriesIntegerToRational_coeff,
    htrunc N]

/-! ### The integer orbit Euler product and the integral lift -/

namespace FiniteOrbitFrobeniusData

/-- `def:weil-integer-orbit-euler-product`.  The integer orbit Euler product
`Z_{orb,D}^ℤ = ∏^lf_O (1 + u_O^ℤ) ∈ ℤ⟦T⟧`. -/
def integerOrbitEulerProduct (D : FiniteOrbitFrobeniusData) : ℤ⟦X⟧ :=
  D.integerOrbitEulerFamily.product

/-- `lemma:weil-integer-orbit-euler-family-rationalization-active-finset`.
Active finsets after rationalizing the integral orbit family:
`A_N((𝓔_D^ℤ)^ℚ) = A_N(𝓔_D)`. -/
theorem integerOrbitEulerFamily_rationalization_activeFinset
    (D : FiniteOrbitFrobeniusData) (N : ℕ) :
    D.integerOrbitEulerFamily.rationalization.activeFinset N =
      D.orbitEulerFamily.activeFinset N := by
  ext O
  rw [TAdicallyLocallyFiniteFamily.mem_activeFinset,
    TAdicallyLocallyFiniteFamily.mem_activeFinset]
  show ¬ PowerSeries.AgreeThrough N
      (D.integerOrbitEulerFamily.rationalComponents O) 0 ↔
    ¬ PowerSeries.AgreeThrough N (D.orbitEulerFactorFamily O) 0
  rw [D.integerOrbitEulerFamily_rationalComponent O]

/-- `lemma:weil-integer-orbit-euler-product-rationalization`.  The
rationalized integral orbit product equals the rational orbit product. -/
theorem integerOrbitEulerProduct_rationalization
    (D : FiniteOrbitFrobeniusData) :
    D.integerOrbitEulerFamily.rationalization.product =
      D.orbitEulerProduct := by
  have htrunc : ∀ N : ℕ,
      D.integerOrbitEulerFamily.rationalization.truncatedProduct N =
        D.orbitEulerFamily.truncatedProduct N := by
    intro N
    rw [TAdicallyLocallyFiniteFamily.truncatedProduct,
      TAdicallyLocallyFiniteFamily.truncatedProduct,
      D.integerOrbitEulerFamily_rationalization_activeFinset N]
    refine Finset.prod_congr rfl fun O _ => ?_
    show 1 + D.integerOrbitEulerFamily.rationalComponents O =
      1 + D.orbitEulerFactorFamily O
    rw [D.integerOrbitEulerFamily_rationalComponent O]
  ext N
  rw [TAdicallyLocallyFiniteFamily.coeff_product, orbitEulerProduct,
    TAdicallyLocallyFiniteFamily.coeff_product, htrunc N]

/-- `lemma:weil-integer-orbit-euler-product-map`.  Scalar image of the
integer orbit Euler product: `ι_*(Z_{orb,D}^ℤ) = Z_{orb,D}`. -/
theorem integerOrbitEulerProduct_map (D : FiniteOrbitFrobeniusData) :
    powerSeriesIntegerToRational D.integerOrbitEulerProduct =
      D.orbitEulerProduct := by
  rw [integerOrbitEulerProduct,
    D.integerOrbitEulerFamily.product_rationalization,
    D.integerOrbitEulerProduct_rationalization]

/-- `lemma:weil-integer-orbit-euler-product-constant`.  The integer orbit
Euler product has constant coefficient one. -/
theorem integerOrbitEulerProduct_constantCoeff (D : FiniteOrbitFrobeniusData) :
    constantCoeff D.integerOrbitEulerProduct = 1 :=
  D.integerOrbitEulerFamily.product_constantCoeff

/-- `prop:weil-counting-zeta-integral-lift`.  Integral lift of the counting
zeta series: `ι_*(Z_{orb,D}^ℤ) = Z_{cnt,D}`. -/
theorem countingZetaSeries_integralLift (D : FiniteOrbitFrobeniusData) :
    powerSeriesIntegerToRational D.integerOrbitEulerProduct =
      D.countingZetaSeries := by
  rw [D.integerOrbitEulerProduct_map, ← D.orbitEulerProduct_eq_countingZeta]

/-! ### The integer degree-grouped Euler product -/

/-- `def:weil-integer-degree-euler-product`.  The integer degree-grouped
Euler product `Z_{deg,D}^ℤ = ∏^lf_{m ∈ ℕ_{>0}} (1 + v_m^ℤ) ∈ ℤ⟦T⟧`. -/
def integerDegreeEulerProduct (D : FiniteOrbitFrobeniusData) : ℤ⟦X⟧ :=
  D.integerDegreeEulerFamily.product

/-- `lemma:weil-integer-degree-rationalized-active-finset`.  Active finsets
after rationalizing the integral degree family:
`A_N((𝓖_D^ℤ)^ℚ) = A_N(𝓖_D)`. -/
theorem integerDegree_rationalizedActiveFinset (D : FiniteOrbitFrobeniusData)
    (N : ℕ) :
    D.integerDegreeEulerFamily.rationalization.activeFinset N =
      D.degreeEulerFamily.activeFinset N := by
  ext m
  rw [TAdicallyLocallyFiniteFamily.mem_activeFinset,
    TAdicallyLocallyFiniteFamily.mem_activeFinset]
  show ¬ PowerSeries.AgreeThrough N
      (D.integerDegreeEulerFamily.rationalComponents m) 0 ↔
    ¬ PowerSeries.AgreeThrough N (D.degreeEulerFactorFamily m) 0
  rw [D.integerDegreeEulerFamily_rationalComponent m]

/-- `lemma:weil-integer-degree-rationalized-truncated-product`.
Rationalized and generic degree truncations agree:
`Π_N((𝓖_D^ℤ)^ℚ) = Π_N(𝓖_D)`. -/
theorem integerDegree_rationalizedTruncatedProduct
    (D : FiniteOrbitFrobeniusData) (N : ℕ) :
    D.integerDegreeEulerFamily.rationalization.truncatedProduct N =
      D.degreeEulerFamily.truncatedProduct N := by
  rw [TAdicallyLocallyFiniteFamily.truncatedProduct,
    TAdicallyLocallyFiniteFamily.truncatedProduct,
    D.integerDegree_rationalizedActiveFinset N]
  refine Finset.prod_congr rfl fun m _ => ?_
  show 1 + D.integerDegreeEulerFamily.rationalComponents m =
    1 + D.degreeEulerFactorFamily m
  rw [D.integerDegreeEulerFamily_rationalComponent m]

/-- `lemma:weil-integer-degree-euler-product-map`.  Scalar image of the
integer degree-grouped Euler product: `ι_*(Z_{deg,D}^ℤ) = Z_{deg,D}`. -/
theorem integerDegreeEulerProduct_map (D : FiniteOrbitFrobeniusData) :
    powerSeriesIntegerToRational D.integerDegreeEulerProduct =
      D.degreeEulerProduct := by
  rw [integerDegreeEulerProduct,
    D.integerDegreeEulerFamily.product_rationalization]
  ext N
  rw [TAdicallyLocallyFiniteFamily.coeff_product, degreeEulerProduct,
    TAdicallyLocallyFiniteFamily.coeff_product,
    D.integerDegree_rationalizedTruncatedProduct N]

/-- `prop:weil-integer-orbit-euler-product-grouped`.  The integer orbit
product regrouped by degree: `Z_{orb,D}^ℤ = Z_{deg,D}^ℤ` in `ℤ⟦T⟧`. -/
theorem integerOrbitEulerProduct_eq_integerDegreeEulerProduct
    (D : FiniteOrbitFrobeniusData) :
    D.integerOrbitEulerProduct = D.integerDegreeEulerProduct := by
  apply powerSeriesIntegerToRational_injective
  rw [D.integerOrbitEulerProduct_map, D.integerDegreeEulerProduct_map]
  exact D.orbitEulerProduct_eq_degreeEulerProduct

end FiniteOrbitFrobeniusData

/-! ### The integral closed-point Euler product -/

namespace ClosedPointOrbitInterface

variable {D : FiniteOrbitFrobeniusData}

/-- `def:weil-integer-closed-point-euler-product`.  The integral
closed-point Euler product `Z_{cl,C}^ℤ = ∏^lf_c (1 + w_c^ℤ) ∈ ℤ⟦T⟧`. -/
def integerEulerProduct (C : ClosedPointOrbitInterface D) : ℤ⟦X⟧ :=
  C.integerEulerFamily.product

/-- `lemma:weil-integer-closed-point-rational-active-finset`.  Active
finsets after rationalizing the integral closed-point family:
`A_N((𝓔_C^ℤ)^ℚ) = A_N(𝓔_C)`. -/
theorem integerEulerFamily_rationalActiveFinset
    (C : ClosedPointOrbitInterface D) (N : ℕ) :
    C.integerEulerFamily.rationalization.activeFinset N =
      C.eulerFamily.activeFinset N := by
  ext c
  rw [TAdicallyLocallyFiniteFamily.mem_activeFinset,
    TAdicallyLocallyFiniteFamily.mem_activeFinset]
  show ¬ PowerSeries.AgreeThrough N
      (C.integerEulerFamily.rationalComponents c) 0 ↔
    ¬ PowerSeries.AgreeThrough N (C.eulerFactorFamily c) 0
  rw [C.integerEulerFamily_rationalComponent c]

/-- `lemma:weil-integer-closed-point-rationalized-product`.  The
rationalized integral closed-point product is the rational closed-point
product. -/
theorem rationalizedIntegerEulerProduct_eq (C : ClosedPointOrbitInterface D) :
    C.integerEulerFamily.rationalization.product = C.eulerProduct := by
  have htrunc : ∀ N : ℕ,
      C.integerEulerFamily.rationalization.truncatedProduct N =
        C.eulerFamily.truncatedProduct N := by
    intro N
    rw [TAdicallyLocallyFiniteFamily.truncatedProduct,
      TAdicallyLocallyFiniteFamily.truncatedProduct,
      C.integerEulerFamily_rationalActiveFinset N]
    refine Finset.prod_congr rfl fun c _ => ?_
    show 1 + C.integerEulerFamily.rationalComponents c =
      1 + C.eulerFactorFamily c
    rw [C.integerEulerFamily_rationalComponent c]
  ext N
  rw [TAdicallyLocallyFiniteFamily.coeff_product, eulerProduct,
    TAdicallyLocallyFiniteFamily.coeff_product, htrunc N]

/-- `lemma:weil-integer-closed-point-euler-product-map`.  Scalar extension
of the integral closed-point Euler product:
`ι_*(Z_{cl,C}^ℤ) = Z_{cl,C}`. -/
theorem integerEulerProduct_map (C : ClosedPointOrbitInterface D) :
    powerSeriesIntegerToRational C.integerEulerProduct = C.eulerProduct := by
  rw [integerEulerProduct, C.integerEulerFamily.product_rationalization,
    C.rationalizedIntegerEulerProduct_eq]

/-- `lemma:weil-integer-closed-point-orbit-rational-image`.  The two
integral products have the same rational image. -/
theorem integerProducts_rationalImage_eq (C : ClosedPointOrbitInterface D) :
    powerSeriesIntegerToRational C.integerEulerProduct =
      powerSeriesIntegerToRational D.integerOrbitEulerProduct := by
  rw [C.integerEulerProduct_map, D.integerOrbitEulerProduct_map,
    C.eulerProduct_eq_orbitEulerProduct]

/-- `prop:weil-integer-closed-point-euler-product-reindex`.  Integral
closed-point/orbit Euler-product reindexing:
`Z_{cl,C}^ℤ = Z_{orb,D}^ℤ` in `ℤ⟦T⟧`. -/
theorem integerEulerProduct_eq_orbitEulerProduct
    (C : ClosedPointOrbitInterface D) :
    C.integerEulerProduct = D.integerOrbitEulerProduct :=
  powerSeriesIntegerToRational_injective C.integerProducts_rationalImage_eq

end ClosedPointOrbitInterface

/-! ### The literal integral zeta certificate -/

namespace FiniteOrbitFrobeniusData

/-- `def:weil-literal-integral-zeta-certificate-type`.  The type of literal
integral zeta certificates over a finite-orbit datum `D` and a
closed-point–orbit interface `C`: three integral power series with the six
named comparison and normalization proofs. -/
structure LiteralIntegralZetaCertificate (D : FiniteOrbitFrobeniusData)
    (C : ClosedPointOrbitInterface D) where
  orbit : ℤ⟦X⟧
  degree : ℤ⟦X⟧
  closed : ℤ⟦X⟧
  orbit_map : powerSeriesIntegerToRational orbit = D.countingZetaSeries
  degree_map : powerSeriesIntegerToRational degree = D.degreeEulerProduct
  orbit_eq_degree : orbit = degree
  closed_map : powerSeriesIntegerToRational closed = C.eulerProduct
  closed_eq_orbit : closed = orbit
  orbit_const : PowerSeries.constantCoeff orbit = 1

/-- `def:weil-literal-integral-zeta-certificate`.  The canonical literal
integral zeta certificate `𝔷^ℤ_{C,D}`, whose data fields are the three
integer Euler products and whose proof fields are the comparison results of
this section. -/
def literalIntegralZetaCertificate (D : FiniteOrbitFrobeniusData)
    (C : ClosedPointOrbitInterface D) :
    D.LiteralIntegralZetaCertificate C where
  orbit := D.integerOrbitEulerProduct
  degree := D.integerDegreeEulerProduct
  closed := C.integerEulerProduct
  orbit_map := D.countingZetaSeries_integralLift
  degree_map := D.integerDegreeEulerProduct_map
  orbit_eq_degree := D.integerOrbitEulerProduct_eq_integerDegreeEulerProduct
  closed_map := C.integerEulerProduct_map
  closed_eq_orbit := C.integerEulerProduct_eq_orbitEulerProduct
  orbit_const := D.integerOrbitEulerProduct_constantCoeff

end FiniteOrbitFrobeniusData

end

end Weil
