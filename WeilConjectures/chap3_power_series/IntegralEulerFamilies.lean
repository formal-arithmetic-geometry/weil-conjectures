/-
Formalization of Chapter 3, Section 7 of `weil_conjectures_chapter3.tex`:
"Integral Euler-family packages for the literal lift"
(`sec:weil-integral-euler-family-packages`).

Every declaration below is annotated with the LaTeX label it formalizes.
Design notes, following the conventions of the earlier section files:

* The coefficient ring is exactly `ℤ` throughout: `E_m^ℤ` is
  `integralInverseEulerFactor m`, and only coefficient-ring-generic
  definitions and lemmas are instantiated — no formal logarithm, division
  by a positive integer, or `ℚ`-algebra structure occurs.
* The initial-vanishing specializations
  (`integerOrbitEulerFactorFamily_agree_zero`,
  `integerDegreeEulerFactorFamily_agree_zero`) are provided as helper
  lemmas, mirroring their rational counterparts in
  `Weil.OrbitEulerProducts`; the text uses these facts inline.
-/
import WeilConjectures.chap3_power_series.ClosedPointInterfaces

open PowerSeries

namespace Weil

noncomputable section

namespace FiniteOrbitFrobeniusData

/-! ### The integer orbit Euler family -/

/-- `def:weil-integer-orbit-euler-factor-family`.  The raw integer orbit
Euler-factor family `u_O^ℤ = E_{deg_F(O)}^ℤ - 1 ∈ ℤ⟦T⟧`. -/
def integerOrbitEulerFactorFamily (D : FiniteOrbitFrobeniusData)
    (O : D.Orbit) : ℤ⟦X⟧ :=
  integralInverseEulerFactor (Orbit.degree O) - 1

/-- `lemma:weil-integer-orbit-euler-factor-family-positive`.  Every integer
orbit component has constant coefficient zero. -/
theorem integerOrbitEulerFactorFamily_positive (D : FiniteOrbitFrobeniusData)
    (O : D.Orbit) :
    constantCoeff (D.integerOrbitEulerFactorFamily O) = 0 :=
  integralInverseEulerFactor_sub_one_constantCoeff (Orbit.degree O)

/-- If `N < deg_F(O)`, then `u_O^ℤ ≡_N 0`; specialization of the raw
integral initial-vanishing lemma. -/
theorem integerOrbitEulerFactorFamily_agree_zero
    (D : FiniteOrbitFrobeniusData) {O : D.Orbit} {N : ℕ}
    (hNd : N < Orbit.degree O) :
    PowerSeries.AgreeThrough N (D.integerOrbitEulerFactorFamily O) 0 :=
  integralInverseEulerFactor_sub_one_agreeThrough hNd

/-- `lemma:weil-integer-orbit-euler-factor-family-locally-finite`.  For
every `N`, only finitely many orbits have `u_O^ℤ ≢_N 0`. -/
theorem integerOrbitEulerFactorFamily_locallyFinite
    (D : FiniteOrbitFrobeniusData) (N : ℕ) :
    {O : D.Orbit |
      ¬ PowerSeries.AgreeThrough N
        (D.integerOrbitEulerFactorFamily O) 0}.Finite := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine Set.Finite.subset Set.finite_empty fun O hO => ?_
    exact absurd (D.integerOrbitEulerFactorFamily_agree_zero O.degree_pos) hO
  · refine Set.Finite.subset (D.boundedOrbitFinset N).finite_toSet
      fun O hO => ?_
    have hdeg : Orbit.degree O ≤ N := by
      by_contra hlt
      exact hO (D.integerOrbitEulerFactorFamily_agree_zero (by omega))
    exact Finset.mem_coe.mpr ((D.mem_boundedOrbitFinset hN O).mpr hdeg)

/-- `def:weil-integer-orbit-euler-locally-finite-family`.  The packaged
integer orbit Euler family `𝓔_D^ℤ` with index type `Orb_F(Ω)` and component
`u_O^ℤ`. -/
def integerOrbitEulerFamily (D : FiniteOrbitFrobeniusData) :
    TAdicallyLocallyFiniteFamily ℤ D.Orbit where
  toFun := D.integerOrbitEulerFactorFamily
  constantCoeff_eq_zero := D.integerOrbitEulerFactorFamily_positive
  finite_active := D.integerOrbitEulerFactorFamily_locallyFinite

/-! ### The integer degree-grouped Euler family -/

/-- `def:weil-integer-degree-euler-factor-family`.  The raw integer
degree-grouped Euler-factor family `v_m^ℤ = (E_m^ℤ)^{a_m(D)} - 1 ∈ ℤ⟦T⟧`. -/
def integerDegreeEulerFactorFamily (D : FiniteOrbitFrobeniusData)
    (m : PositiveDegreeIndex) : ℤ⟦X⟧ :=
  integralInverseEulerFactor (m : ℕ) ^ D.orbitCount (m : ℕ) - 1

/-- `lemma:weil-integer-degree-euler-factor-family-positive`.  Every integer
degree component has constant coefficient zero. -/
theorem integerDegreeEulerFactorFamily_positive
    (D : FiniteOrbitFrobeniusData) (m : PositiveDegreeIndex) :
    constantCoeff (D.integerDegreeEulerFactorFamily m) = 0 := by
  rw [integerDegreeEulerFactorFamily, map_sub, map_one, map_pow,
    integralInverseEulerFactor_constantCoeff m.2, one_pow, sub_self]

/-- If `N < (m : ℕ)`, then `v_m^ℤ ≡_N 0`: the raw integral inverse Euler
factor agrees with one through `N`, hence so does its `a_m(D)`-th power. -/
theorem integerDegreeEulerFactorFamily_agree_zero
    (D : FiniteOrbitFrobeniusData) {m : PositiveDegreeIndex} {N : ℕ}
    (hNm : N < (m : ℕ)) :
    PowerSeries.AgreeThrough N (D.integerDegreeEulerFactorFamily m) 0 := by
  have hE : PowerSeries.AgreeThrough N
      (integralInverseEulerFactor (m : ℕ)) 1 := by
    have h := PowerSeries.AgreeThrough.one_add
      (integralInverseEulerFactor_sub_one_agreeThrough hNm)
    rwa [show (1 : ℤ⟦X⟧) + (integralInverseEulerFactor (m : ℕ) - 1) =
        integralInverseEulerFactor (m : ℕ) by ring] at h
  have hpow := hE.pow (D.orbitCount (m : ℕ))
  rw [one_pow] at hpow
  have hsub := hpow.sub (PowerSeries.AgreeThrough.refl N 1)
  rwa [sub_self] at hsub

/-- `lemma:weil-integer-degree-euler-factor-family-locally-finite`.  For
every `N`, only finitely many positive degrees have `v_m^ℤ ≢_N 0`. -/
theorem integerDegreeEulerFactorFamily_locallyFinite
    (D : FiniteOrbitFrobeniusData) (N : ℕ) :
    {m : PositiveDegreeIndex |
      ¬ PowerSeries.AgreeThrough N
        (D.integerDegreeEulerFactorFamily m) 0}.Finite := by
  refine Set.Finite.subset (positiveDegreeIndexFinset N).finite_toSet
    fun m hm => ?_
  refine Finset.mem_coe.mpr ((mem_positiveDegreeIndexFinset m).mpr ?_)
  by_contra hNm
  exact hm (D.integerDegreeEulerFactorFamily_agree_zero (by omega))

/-- `def:weil-integer-degree-euler-locally-finite-family`.  The packaged
integer degree-grouped Euler family `𝓖_D^ℤ` indexed by positive degrees,
with component `v_m^ℤ`. -/
def integerDegreeEulerFamily (D : FiniteOrbitFrobeniusData) :
    TAdicallyLocallyFiniteFamily ℤ PositiveDegreeIndex where
  toFun := D.integerDegreeEulerFactorFamily
  constantCoeff_eq_zero := D.integerDegreeEulerFactorFamily_positive
  finite_active := D.integerDegreeEulerFactorFamily_locallyFinite

end FiniteOrbitFrobeniusData

/-! ### The integer closed-point Euler family -/

namespace ClosedPointOrbitInterface

open FiniteOrbitFrobeniusData

variable {D : FiniteOrbitFrobeniusData}

/-- `def:weil-integer-closed-point-euler-factor-family`.  The raw integer
closed-point Euler-factor family `w_c^ℤ = E_{deg_C(c)}^ℤ - 1 ∈ ℤ⟦T⟧`. -/
def integerEulerFactorFamily (C : ClosedPointOrbitInterface D)
    (c : C.ClosedPoint) : ℤ⟦X⟧ :=
  integralInverseEulerFactor (C.degree c) - 1

/-- `lemma:weil-integer-closed-point-euler-factor-family-positive`.  Every
integer closed-point component has constant coefficient zero. -/
theorem integerEulerFactorFamily_positive (C : ClosedPointOrbitInterface D)
    (c : C.ClosedPoint) :
    constantCoeff (C.integerEulerFactorFamily c) = 0 :=
  integralInverseEulerFactor_sub_one_constantCoeff (C.degree c)

/-- `lemma:weil-integer-closed-point-euler-component-transport`.  Integer
closed-point components transport to orbit components:
`u_{θ_C(c)}^ℤ = w_c^ℤ`. -/
theorem integerEulerFactorFamily_component_transport
    (C : ClosedPointOrbitInterface D) (c : C.ClosedPoint) :
    D.integerOrbitEulerFactorFamily (C.theta c) =
      C.integerEulerFactorFamily c := by
  rw [FiniteOrbitFrobeniusData.integerOrbitEulerFactorFamily,
    integerEulerFactorFamily, ← C.degree_eq c]

/-- `lemma:weil-integer-closed-point-active-image-subset`.  Active integer
closed points map into active integer orbits. -/
theorem integerActiveClosed_image_subset_activeOrbit
    (C : ClosedPointOrbitInterface D) (N : ℕ) :
    C.theta ''
        {c | ¬ PowerSeries.AgreeThrough N (C.integerEulerFactorFamily c) 0} ⊆
      {O | ¬ PowerSeries.AgreeThrough N
        (D.integerOrbitEulerFactorFamily O) 0} := by
  rintro O ⟨c, hc, rfl⟩
  show ¬ PowerSeries.AgreeThrough N
    (D.integerOrbitEulerFactorFamily (C.theta c)) 0
  rw [C.integerEulerFactorFamily_component_transport c]
  exact hc

/-- `lemma:weil-integer-closed-point-active-image-finite`.  The active
integer closed-point image is finite. -/
theorem integerActiveClosed_image_finite (C : ClosedPointOrbitInterface D)
    (N : ℕ) :
    (C.theta ''
      {c | ¬ PowerSeries.AgreeThrough N
        (C.integerEulerFactorFamily c) 0}).Finite :=
  Set.Finite.subset (D.integerOrbitEulerFactorFamily_locallyFinite N)
    (C.integerActiveClosed_image_subset_activeOrbit N)

/-- `lemma:weil-integer-closed-point-euler-factor-family-locally-finite`.
For every `N`, only finitely many closed points have `w_c^ℤ ≢_N 0`. -/
theorem integerEulerFactorFamily_locallyFinite
    (C : ClosedPointOrbitInterface D) (N : ℕ) :
    {c : C.ClosedPoint |
      ¬ PowerSeries.AgreeThrough N
        (C.integerEulerFactorFamily c) 0}.Finite :=
  Set.Finite.of_finite_image (C.integerActiveClosed_image_finite N)
    C.theta.injective.injOn

/-- `def:weil-integer-closed-point-euler-locally-finite-family`.  The
packaged integer closed-point Euler family `𝓔_C^ℤ` indexed by closed
points, with component `w_c^ℤ`. -/
def integerEulerFamily (C : ClosedPointOrbitInterface D) :
    TAdicallyLocallyFiniteFamily ℤ C.ClosedPoint where
  toFun := C.integerEulerFactorFamily
  constantCoeff_eq_zero := C.integerEulerFactorFamily_positive
  finite_active := C.integerEulerFactorFamily_locallyFinite

end ClosedPointOrbitInterface

end

end Weil
