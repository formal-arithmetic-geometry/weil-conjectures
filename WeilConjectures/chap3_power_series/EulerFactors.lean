/-
Formalization of Chapter 3, Section 3 of `weil_conjectures_chapter3.tex`:
"Single Euler factors" (`sec:weil-euler-products`).

Every declaration below is annotated with the LaTeX label it formalizes.
Design notes, following the conventions of `Weil.FormalExpLog`:

* Per the "Generic Euler-factor scope" paragraph, the raw inverse Euler
  factor lives in `ℤ⟦X⟧` and is transported to an arbitrary commutative ring
  `R` along `Int.castRingHom R`; no rational scalars enter before the
  "Rational Euler-logarithm scope" paragraph, from which point the
  coefficient ring is literally `ℚ`.
* Two-part tex statements are provided as separate component lemmas (for
  downstream use) together with the bundled conjunction under the tex name.
* The scalar `(m : ℚ)T^{m-1}` of the text is rendered as
  `(m : ℚ⟦X⟧) * X ^ (m - 1)`, the natural-number cast into the power-series
  ring, which is exactly the form produced by `PowerSeries.derivative_pow`.
-/
module

public import WeilConjectures.chap3_power_series.FormalExpLog
public import WeilConjectures.chap3_power_series.LocallyFiniteProducts

@[expose] public section

open PowerSeries

namespace Weil

noncomputable section

variable {R : Type*} [CommRing R]

/-! ### Generic Euler-factor scope -/

/-- `def:weil-integral-inverse-euler-factor`.  The raw integral inverse Euler
factor `E_m^ℤ = ∑_{m ∣ n} T^n ∈ ℤ⟦T⟧`, defined coefficientwise as a total
function of `m`. -/
def integralInverseEulerFactor (m : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => if m ∣ n then 1 else 0

/-- `lemma:weil-integral-inverse-euler-factor-coeff`.  Coefficient formula for
the raw integral inverse Euler factor. -/
theorem coeff_integralInverseEulerFactor {m : ℕ} (_hm : 1 ≤ m) (n : ℕ) :
    coeff n (integralInverseEulerFactor m) = if m ∣ n then 1 else 0 := by
  rw [integralInverseEulerFactor, coeff_mk]

/-- `lemma:weil-integral-inverse-euler-factor-constant`.  Constant coefficient
of the raw integral inverse Euler factor. -/
theorem integralInverseEulerFactor_constantCoeff {m : ℕ} (hm : 1 ≤ m) :
    constantCoeff (integralInverseEulerFactor m) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_integralInverseEulerFactor hm,
    if_pos (dvd_zero m)]

/-- `lemma:weil-integral-inverse-euler-factor-initial-vanishing`,
constant-coefficient part: `c(E_m^ℤ - 1) = 0`. -/
theorem integralInverseEulerFactor_sub_one_constantCoeff (m : ℕ) :
    constantCoeff (integralInverseEulerFactor m - 1) = 0 := by
  rw [map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply,
    integralInverseEulerFactor, coeff_mk, if_pos (dvd_zero m), sub_self]

/-- `lemma:weil-integral-inverse-euler-factor-initial-vanishing`,
agreement part: if `N < m`, then `E_m^ℤ - 1 ≡_N 0`. -/
theorem integralInverseEulerFactor_sub_one_agreeThrough {m N : ℕ} (hNm : N < m) :
    PowerSeries.AgreeThrough N (integralInverseEulerFactor m - 1) 0 := by
  intro j hj
  rw [map_zero, map_sub, integralInverseEulerFactor, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [if_pos (dvd_zero m), if_pos rfl, sub_self]
  · rw [if_neg fun hd => absurd (Nat.le_of_dvd hj0 hd) (by omega),
      if_neg (by omega), sub_zero]

/-- `lemma:weil-integral-inverse-euler-factor-initial-vanishing`, bundled as
in the text. -/
theorem integralInverseEulerFactor_sub_one_agree_zero (m : ℕ) :
    constantCoeff (integralInverseEulerFactor m - 1) = 0 ∧
      ∀ N : ℕ, N < m →
        PowerSeries.AgreeThrough N (integralInverseEulerFactor m - 1) 0 :=
  ⟨integralInverseEulerFactor_sub_one_constantCoeff m,
    fun _ hNm => integralInverseEulerFactor_sub_one_agreeThrough hNm⟩

/-- `def:weil-inverse-euler-factor`.  The scalar extension
`E_{m,R} = map (Int.castRingHom R) E_m^ℤ ∈ R⟦T⟧` of the raw integral inverse
Euler factor. -/
def inverseEulerFactor (R : Type*) [CommRing R] (m : ℕ) : R⟦X⟧ :=
  PowerSeries.map (Int.castRingHom R) (integralInverseEulerFactor m)

/-- `lemma:weil-inverse-euler-factor-coeff`, coefficient part.  Coefficient
formula for a scalar-extended inverse Euler factor. -/
theorem coeff_inverseEulerFactor {m : ℕ} (_hm : 1 ≤ m) (n : ℕ) :
    coeff n (inverseEulerFactor R m) = if m ∣ n then 1 else 0 := by
  rw [inverseEulerFactor, coeff_map, integralInverseEulerFactor, coeff_mk]
  split_ifs <;> simp

/-- `lemma:weil-inverse-euler-factor-coeff`, support part.  Over a nontrivial
ring the coefficient support of `E_{m,R}` (`m > 0`) is precisely the set of
multiples of `m`; this is a reformulation of the coefficient formula. -/
theorem inverseEulerFactor_support [Nontrivial R] {m : ℕ} (hm : 0 < m) :
    (Function.support fun n => coeff n (inverseEulerFactor R m)) =
      Set.range fun r => m * r := by
  ext n
  simp only [Function.mem_support, ne_eq, Set.mem_range,
    coeff_inverseEulerFactor hm]
  constructor
  · intro h
    have hd : m ∣ n := by
      by_contra hnd
      rw [if_neg hnd] at h
      exact h rfl
    obtain ⟨r, hr⟩ := hd
    exact ⟨r, hr.symm⟩
  · rintro ⟨r, rfl⟩
    rw [if_pos ⟨r, rfl⟩]
    exact one_ne_zero

/-- `lemma:weil-inverse-euler-factor-constant`.  Constant coefficient of an
inverse Euler factor. -/
theorem inverseEulerFactor_constantCoeff {m : ℕ} (hm : 1 ≤ m) :
    constantCoeff (inverseEulerFactor R m) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_inverseEulerFactor hm,
    if_pos (dvd_zero m)]

/-- `lemma:weil-inverse-euler-factor-mul`.  The inverse identity
`(1 - T^m)E_m = 1 = E_m(1 - T^m)` for a single Euler factor. -/
theorem one_sub_X_pow_mul_inverseEulerFactor {m : ℕ} (hm : 1 ≤ m) :
    (1 - X ^ m) * inverseEulerFactor R m = 1 ∧
      inverseEulerFactor R m * (1 - X ^ m) = 1 := by
  have key : inverseEulerFactor R m * (1 - X ^ m) = 1 := by
    ext n
    rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one,
      coeff_inverseEulerFactor hm]
    by_cases hmn : m ≤ n
    · rw [if_pos hmn, coeff_inverseEulerFactor hm, if_neg (show ¬n = 0 by omega)]
      by_cases hd : m ∣ n
      · rw [if_pos hd, if_pos (Nat.dvd_sub hd dvd_rfl), sub_self]
      · have hnd : ¬m ∣ n - m := by
          intro hd'
          apply hd
          have h2 := Nat.dvd_add hd' (dvd_refl m)
          rwa [Nat.sub_add_cancel hmn] at h2
        rw [if_neg hd, if_neg hnd, sub_zero]
    · rw [if_neg hmn]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [if_pos (dvd_zero m), if_pos rfl, sub_zero]
      · rw [if_neg fun hd => hmn (Nat.le_of_dvd hn hd),
          if_neg (show ¬n = 0 by omega), sub_zero]
  exact ⟨by rw [mul_comm]; exact key, key⟩

/-- `def:weil-inverse-euler-factor-positive-part`.  The positive part
`e_m = E_m - 1` of an inverse Euler factor. -/
def inverseEulerFactorPositivePart (R : Type*) [CommRing R] (m : ℕ) : R⟦X⟧ :=
  inverseEulerFactor R m - 1

/-- `lemma:weil-inverse-euler-factor-initial-vanishing`,
constant-coefficient part: `c(e_m) = 0`. -/
theorem inverseEulerFactorPositivePart_constantCoeff (m : ℕ) :
    constantCoeff (inverseEulerFactorPositivePart R m) = 0 := by
  have h : constantCoeff (inverseEulerFactor R m) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, inverseEulerFactor, coeff_map,
      integralInverseEulerFactor, coeff_mk, if_pos (dvd_zero m), map_one]
  rw [inverseEulerFactorPositivePart, map_sub, map_one, h, sub_self]

/-- `lemma:weil-inverse-euler-factor-initial-vanishing`, agreement part:
if `N < m`, then `e_m ≡_N 0`. -/
theorem inverseEulerFactorPositivePart_agreeThrough {m N : ℕ} (hNm : N < m) :
    PowerSeries.AgreeThrough N (inverseEulerFactorPositivePart R m) 0 := by
  have hm : 1 ≤ m := by omega
  intro j hj
  rw [map_zero, inverseEulerFactorPositivePart, map_sub,
    coeff_inverseEulerFactor hm, coeff_one]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [if_pos (dvd_zero m), if_pos rfl, sub_self]
  · rw [if_neg fun hd => absurd (Nat.le_of_dvd hj0 hd) (by omega),
      if_neg (by omega), sub_zero]

/-- `lemma:weil-inverse-euler-factor-initial-vanishing`, bundled as in the
text. -/
theorem inverseEulerFactorPositivePart_agree_zero (m : ℕ) :
    constantCoeff (inverseEulerFactorPositivePart R m) = 0 ∧
      ∀ N : ℕ, N < m →
        PowerSeries.AgreeThrough N (inverseEulerFactorPositivePart R m) 0 :=
  ⟨inverseEulerFactorPositivePart_constantCoeff m,
    fun _ hNm => inverseEulerFactorPositivePart_agreeThrough hNm⟩

/-- `lemma:weil-inverse-euler-factor-activation`.  Over a nontrivial ring,
`e_m` fails to agree with `0` through any `N ≥ m ≥ 1`. -/
theorem inverseEulerFactorPositivePart_not_agree_zero [Nontrivial R] {m N : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) :
    ¬PowerSeries.AgreeThrough N (inverseEulerFactorPositivePart R m) 0 := by
  intro h
  have hcm := h m hmN
  rw [map_zero, inverseEulerFactorPositivePart, map_sub,
    coeff_inverseEulerFactor hm, if_pos dvd_rfl, coeff_one,
    if_neg (show ¬m = 0 by omega), sub_zero] at hcm
  exact one_ne_zero hcm

/-! ### Rational Euler-logarithm scope

Per the scope paragraph of the text, from here on the coefficient ring is
literally `ℚ`; `n / m` below is the total natural-number quotient, cast into
`ℚ` before the outer division. -/

/-- `def:weil-euler-log-series`.  The logarithm series
`L_m = ∑_{r ≥ 1} T^{mr}/r ∈ ℚ⟦T⟧` of a single Euler factor, defined
coefficientwise; no ambient infinite-sum operation is used. -/
def eulerLogSeries (m : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if 0 < n ∧ m ∣ n then (1 : ℚ) / ((n / m : ℕ) : ℚ) else 0

/-- Coefficient formula of `def:weil-euler-log-series`, restated through
`PowerSeries.coeff_mk` for rewriting. -/
theorem coeff_eulerLogSeries (m n : ℕ) :
    coeff n (eulerLogSeries m) =
      if 0 < n ∧ m ∣ n then (1 : ℚ) / ((n / m : ℕ) : ℚ) else 0 := by
  rw [eulerLogSeries, coeff_mk]

/-- `lemma:weil-euler-log-shift-divisibility`.  Shifted divisibility for Euler
coefficients: for `m ≥ 1`, `m ∣ n + 1 ↔ m - 1 ≤ n ∧ m ∣ n - (m - 1)`. -/
theorem dvd_succ_iff_pred_le_and_dvd_sub_pred {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    m ∣ n + 1 ↔ m - 1 ≤ n ∧ m ∣ n - (m - 1) := by
  constructor
  · intro h
    have hle : m ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) h
    refine ⟨by omega, ?_⟩
    have h2 : m ∣ n + 1 - m := Nat.dvd_sub h dvd_rfl
    rwa [show n + 1 - m = n - (m - 1) by omega] at h2
  · rintro ⟨hle, hdvd⟩
    have h2 : m ∣ m + (n - (m - 1)) := Nat.dvd_add dvd_rfl hdvd
    rwa [show m + (n - (m - 1)) = n + 1 by omega] at h2

/-- `lemma:weil-euler-log-series-derivative`, constant-coefficient part:
`c(L_m) = 0`. -/
theorem eulerLogSeries_constantCoeff (m : ℕ) :
    constantCoeff (eulerLogSeries m) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_eulerLogSeries,
    if_neg fun h => lt_irrefl 0 h.1]

/-- `lemma:weil-euler-log-series-derivative`, derivative part:
`D L_m = (m : ℚ)T^{m-1}E_m`. -/
theorem derivative_eulerLogSeries {m : ℕ} (hm : 1 ≤ m) :
    formalDerivative (eulerLogSeries m) =
      (m : ℚ⟦X⟧) * X ^ (m - 1) * inverseEulerFactor ℚ m := by
  ext n
  rw [formalDerivative_coeff, coeff_eulerLogSeries,
    show ((m : ℕ) : ℚ⟦X⟧) = C (m : ℚ) from (map_natCast (C : ℚ →+* ℚ⟦X⟧) m).symm,
    mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  by_cases hd : m ∣ n + 1
  · obtain ⟨hle, hdvd⟩ := (dvd_succ_iff_pred_le_and_dvd_sub_pred hm n).mp hd
    rw [if_pos ⟨Nat.succ_pos n, hd⟩, if_pos hle, coeff_inverseEulerFactor hm,
      if_pos hdvd, mul_one]
    have hq : 0 < (n + 1) / m := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos n) hd) (by omega)
    have hqQ : (((n + 1) / m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : ((n : ℚ) + 1) = (m : ℚ) * (((n + 1) / m : ℕ) : ℚ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hd]
      push_cast
      ring
    rw [hcast]
    field_simp
  · rw [if_neg fun hcon => hd hcon.2]
    by_cases hle : m - 1 ≤ n
    · rw [if_pos hle, coeff_inverseEulerFactor hm,
        if_neg fun hdvd =>
          hd ((dvd_succ_iff_pred_le_and_dvd_sub_pred hm n).mpr ⟨hle, hdvd⟩),
        mul_zero, mul_zero]
    · rw [if_neg hle, mul_zero, mul_zero]

/-- `lemma:weil-euler-log-series-derivative`, bundled as in the text. -/
theorem eulerLogSeries_derivative {m : ℕ} (hm : 1 ≤ m) :
    constantCoeff (eulerLogSeries m) = 0 ∧
      formalDerivative (eulerLogSeries m) =
        (m : ℚ⟦X⟧) * X ^ (m - 1) * inverseEulerFactor ℚ m :=
  ⟨eulerLogSeries_constantCoeff m, derivative_eulerLogSeries hm⟩

/-- `lemma:weil-formal-derivative-X-pow`.  Derivative of a power-series
monomial: `D(T^m) = (m : ℚ)T^{m-1}`. -/
theorem formalDerivative_X_pow (m : ℕ) :
    formalDerivative (X ^ m : ℚ⟦X⟧) = (m : ℚ⟦X⟧) * X ^ (m - 1) := by
  rw [formalDerivative, derivative_pow, derivative_X, mul_one]

/-- `lemma:weil-inverse-euler-factor-derivative`.  Derivative of an inverse
Euler factor: `D E_m = (m : ℚ)T^{m-1}E_m²`. -/
theorem inverseEulerFactor_derivative {m : ℕ} (hm : 1 ≤ m) :
    formalDerivative (inverseEulerFactor ℚ m) =
      (m : ℚ⟦X⟧) * X ^ (m - 1) * inverseEulerFactor ℚ m ^ 2 := by
  have h1 := (one_sub_X_pow_mul_inverseEulerFactor (R := ℚ) hm).2
  have hd := congrArg formalDerivative h1
  rw [formalDerivative_mul, formalDerivative_one] at hd
  have hsub : formalDerivative ((1 : ℚ⟦X⟧) - X ^ m) =
      -((m : ℚ⟦X⟧) * X ^ (m - 1)) := by
    have h0 : formalDerivative ((1 : ℚ⟦X⟧) - X ^ m) =
        formalDerivative (1 : ℚ⟦X⟧) - formalDerivative (X ^ m : ℚ⟦X⟧) := by
      simp only [formalDerivative, map_sub]
    rw [h0, formalDerivative_one, formalDerivative_X_pow, zero_sub]
  rw [hsub] at hd
  linear_combination inverseEulerFactor ℚ m * hd -
    formalDerivative (inverseEulerFactor ℚ m) * h1

/-- `lemma:weil-exp-euler-log-series-ode`.  The exponential Euler series
satisfies the Euler ODE `D Exp(L_m) = ((m : ℚ)T^{m-1}E_m) Exp(L_m)`. -/
theorem formalExp_eulerLogSeries_ode {m : ℕ} (hm : 1 ≤ m) :
    formalDerivative (formalExp (eulerLogSeries m)) =
      (m : ℚ⟦X⟧) * X ^ (m - 1) * inverseEulerFactor ℚ m *
        formalExp (eulerLogSeries m) := by
  rw [formalExp_derivative (eulerLogSeries_constantCoeff m),
    derivative_eulerLogSeries hm]

/-- `lemma:weil-inverse-euler-factor-ode`.  The inverse Euler factor satisfies
the Euler ODE `D E_m = ((m : ℚ)T^{m-1}E_m) E_m`. -/
theorem inverseEulerFactor_ode {m : ℕ} (hm : 1 ≤ m) :
    formalDerivative (inverseEulerFactor ℚ m) =
      (m : ℚ⟦X⟧) * X ^ (m - 1) * inverseEulerFactor ℚ m *
        inverseEulerFactor ℚ m := by
  rw [inverseEulerFactor_derivative hm]
  ring

/-- `lemma:weil-exp-euler-log-series`.  Exponential of the Euler logarithm:
`Exp(L_m) = E_m`. -/
theorem formalExp_eulerLogSeries {m : ℕ} (hm : 1 ≤ m) :
    formalExp (eulerLogSeries m) = inverseEulerFactor ℚ m :=
  eq_of_same_logarithmicDerivative
    (formalExp_constantCoeff (eulerLogSeries_constantCoeff m))
    (inverseEulerFactor_constantCoeff hm)
    (formalExp_eulerLogSeries_ode hm)
    (inverseEulerFactor_ode hm)

/-- `def:weil-bundled-inverse-euler-factor`.  The bundled normalized inverse
Euler factor `Ê_m ∈ OneSeries(ℚ)`; by proof irrelevance the value is
independent of the witness `1 ≤ m`. -/
def normalizedInverseEulerFactor (m : ℕ) (hm : 1 ≤ m) : OneSeries ℚ :=
  ⟨inverseEulerFactor ℚ m, inverseEulerFactor_constantCoeff hm⟩

/-- `lemma:weil-log-inverse-euler-factor`.  Logarithm of an inverse Euler
factor: `Log(Ê_m) = L_m`.  Since `formalLog` is defined on raw power series,
the statement is phrased through the underlying series of `Ê_m`. -/
theorem formalLog_inverseEulerFactor {m : ℕ} (hm : 1 ≤ m) :
    formalLog ((normalizedInverseEulerFactor m hm : OneSeries ℚ) : ℚ⟦X⟧) =
      eulerLogSeries m := by
  show formalLog (inverseEulerFactor ℚ m) = eulerLogSeries m
  rw [← formalExp_eulerLogSeries hm,
    formalLog_formalExp (eulerLogSeries_constantCoeff m)]

/-- `lemma:weil-rational-reciprocal-divisor-quotient`.  Rational reciprocal of
a divisor quotient: `1/((n/m : ℕ) : ℚ) = (m : ℚ)/(n : ℚ)` for `m ∣ n`. -/
theorem one_div_natDiv_cast {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hd : m ∣ n) :
    (1 : ℚ) / ((n / m : ℕ) : ℚ) = (m : ℚ) / (n : ℚ) := by
  have hq : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hd) hm
  have h1 : ((n / m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_eq_div_iff h1 h2, one_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hd]

end

end Weil
