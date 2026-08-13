/-
Formalization of Chapter 3, Section 1 of `weil_conjectures_chapter3.tex`:
"Coefficientwise exponential and logarithm"
(`sec:weil-formal-series`).

Every declaration below is annotated with the LaTeX label it formalizes.
Design notes, following the "Formalization note" conventions of the guideline:

* `PositiveSeries R` and `OneSeries R` are the subtypes `TR[[T]]` and
  `OneSeries(R)` of the text.  Since `PowerSeries.subst` is a total function
  in mathlib (the substitution certificate `PowerSeries.HasSubst` is only
  needed to *prove* things about it), the operations `formalExp`, `formalLog`,
  `geometricInverse`, `geometricComparisonSeries` are defined on raw power
  series, and each lemma carries the constant-coefficient hypothesis of its
  statement scope, exactly as in the text ("If c(A)=1, then ...").  Proof
  irrelevance, invoked in the text to make the notation independent of the
  chosen certificate, is thereby automatic.
* The two-part statements of the text (`lemma:weil-formal-derivative-rules`,
  `lemma:weil-formal-log-coeff`, `lemma:weil-geometric-inverse-mul`) are
  provided as separate component lemmas (for downstream use) and, where the
  text states a single declaration, also as the bundled conjunction.
* The chapter-wide scope is an arbitrary commutative ring `R`; from the
  "Rational coefficient scope" paragraph on, the parameters are
  `[CommRing R] [Algebra ℚ R] [IsAddTorsionFree R]`.
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

open PowerSeries Nat

namespace Weil

noncomputable section

variable {R : Type*} [CommRing R]

/-! ### Generic coefficient-ring scope -/

/-- `def:weil-positive-series`.  The subtype `TR[[T]] = {U : R[[T]] | c(U) = 0}`
of positive-order formal series. -/
abbrev PositiveSeries (R : Type*) [CommRing R] : Type _ :=
  {U : R⟦X⟧ // constantCoeff U = 0}

/-- `def:weil-positive-series-zero`.  The zero positive-order series. -/
instance PositiveSeries.instZero : Zero (PositiveSeries R) :=
  ⟨⟨0, map_zero _⟩⟩

/-- `def:weil-positive-series-add`.  Addition of positive-order series; the
closure certificate is `map_add` for the constant-coefficient ring
homomorphism together with the certificates carried by the summands. -/
instance PositiveSeries.instAdd : Add (PositiveSeries R) :=
  ⟨fun U V => ⟨(U : R⟦X⟧) + V, by rw [map_add, U.2, V.2, add_zero]⟩⟩

/-- `def:weil-one-series`.  The subtype `OneSeries(R) = {A : R[[T]] | c(A) = 1}`
of normalized one-series. -/
abbrev OneSeries (R : Type*) [CommRing R] : Type _ :=
  {A : R⟦X⟧ // constantCoeff A = 1}

/-- `def:weil-one-series-one`.  The identity normalized one-series. -/
instance OneSeries.instOne : One (OneSeries R) :=
  ⟨⟨1, map_one _⟩⟩

/-- `def:weil-one-series-mul`.  Multiplication of normalized one-series; the
closure certificate is `map_mul` for the constant-coefficient ring
homomorphism together with the certificates carried by the factors. -/
instance OneSeries.instMul : Mul (OneSeries R) :=
  ⟨fun A B => ⟨(A : R⟦X⟧) * B, by rw [map_mul, A.2, B.2, mul_one]⟩⟩

/-- `lemma:weil-positive-series-has-subst`.  A positive-order series admits
formal substitution in the sense of `PowerSeries.subst`. -/
theorem PositiveSeries.hasSubst (U : PositiveSeries R) : HasSubst (U : R⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' U.2

/-- `lemma:weil-positive-series-pow-coeff-zero`, in unbundled form.
Low coefficients of powers of a positive-order series vanish:
if `N < r`, then `[T^N] U^r = 0`. -/
theorem PositiveSeries.coeff_pow_eq_zero_of_lt {U : R⟦X⟧}
    (hU : constantCoeff U = 0) {N r : ℕ} (h : N < r) : coeff N (U ^ r) = 0 := by
  induction r generalizing N with
  | zero => exact absurd h (Nat.not_lt_zero N)
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rcases Nat.eq_zero_or_pos p.2 with h2 | h2
    · rw [h2, coeff_zero_eq_constantCoeff_apply, hU, mul_zero]
    · rw [ih (by omega), zero_mul]

/-! ### Rational coefficient scope

For the remaining declarations of the section the parameters are
`[CommRing R] [Algebra ℚ R] [IsAddTorsionFree R]`.  Per the scope paragraph
of the text, this parameter envelope is part of every remaining statement,
so the unused-section-variable linter is silenced instead of narrowing
individual declarations. -/

variable [Algebra ℚ R] [IsAddTorsionFree R]

set_option linter.unusedSectionVars false

/-- `def:weil-formal-exp`.  The coefficientwise formal exponential
`Exp(U) = (PowerSeries.exp R)|_{X = U}`, substitution of a formal power
series (not an analytic exponential). -/
def formalExp (U : R⟦X⟧) : R⟦X⟧ :=
  (PowerSeries.exp R).subst U

/-- `lemma:weil-formal-exp-coeff`.  Finite coefficient formula for the formal
exponential. -/
theorem formalExp_coeff {U : R⟦X⟧} (hU : constantCoeff U = 0) (N : ℕ) :
    coeff N (formalExp U) =
      ∑ r ∈ Finset.range (N + 1), algebraMap ℚ R (1 / r !) * coeff N (U ^ r) := by
  have hs : HasSubst U := HasSubst.of_constantCoeff_zero' hU
  have hsupp : (Function.support fun d => coeff d (exp R) • coeff N (U ^ d)) ⊆
      ↑(Finset.range (N + 1)) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hdN
    exact hd (by rw [PositiveSeries.coeff_pow_eq_zero_of_lt hU (by omega), smul_zero])
  rw [formalExp, coeff_subst' hs, finsum_eq_finsetSum_of_support_subset _ hsupp]
  exact Finset.sum_congr rfl fun r _ => by rw [coeff_exp, smul_eq_mul]

/-- `lemma:weil-formal-exp-constant`.  Constant coefficient of the formal
exponential. -/
theorem formalExp_constantCoeff {U : R⟦X⟧} (hU : constantCoeff U = 0) :
    constantCoeff (formalExp U) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, formalExp_coeff hU]
  simp

/-- `def:weil-formal-log-outer-series`.  The universal outer logarithm series
`Λ_R`, with coefficient `(-1)^{r+1}/r` in each positive degree `r` and `0` in
degree zero.  The construction does not depend on a library-provided
logarithm series. -/
def formalLogOuter (R : Type*) [CommRing R] [Algebra ℚ R] : R⟦X⟧ :=
  PowerSeries.mk fun r =>
    if r = 0 then 0 else algebraMap ℚ R ((-1) ^ (r + 1) / (r : ℚ))

/-- `lemma:weil-formal-log-outer-series-coeff`.  Coefficients of the universal
outer logarithm. -/
theorem coeff_formalLogOuter (r : ℕ) :
    coeff r (formalLogOuter R) =
      if r = 0 then 0 else algebraMap ℚ R ((-1) ^ (r + 1) / (r : ℚ)) := by
  rw [formalLogOuter, coeff_mk]

/-- `def:weil-formal-log`.  The coefficientwise formal logarithm
`Log(A) = Λ_R|_{X = A - 1}`. -/
def formalLog (A : R⟦X⟧) : R⟦X⟧ :=
  (formalLogOuter R).subst (A - 1)

/-- The reduced part of a one-series has constant coefficient zero. -/
theorem constantCoeff_sub_one_eq_zero {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    constantCoeff (A - 1) = 0 := by
  rw [map_sub, hA, map_one, sub_self]

/-- `lemma:weil-formal-log-coeff`, degree-zero part: `[T^0] Log(A) = 0`. -/
theorem formalLog_constantCoeff {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    constantCoeff (formalLog A) = 0 := by
  have hU := constantCoeff_sub_one_eq_zero hA
  have hs : HasSubst (A - 1) := HasSubst.of_constantCoeff_zero' hU
  rw [← coeff_zero_eq_constantCoeff_apply, formalLog, coeff_subst' hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [coeff_formalLogOuter, if_pos rfl, zero_smul]
  · rw [coeff_zero_eq_constantCoeff_apply, map_pow, hU, zero_pow (by omega), smul_zero]

/-- `lemma:weil-formal-log-coeff`, positive-degree part.  Finite coefficient
formula for the formal logarithm. -/
theorem formalLog_coeff {A : R⟦X⟧} (hA : constantCoeff A = 1) {N : ℕ} (_hN : N ≠ 0) :
    coeff N (formalLog A) =
      ∑ r ∈ Finset.Icc 1 N,
        algebraMap ℚ R ((-1) ^ (r + 1) / (r : ℚ)) * coeff N ((A - 1) ^ r) := by
  have hU := constantCoeff_sub_one_eq_zero hA
  have hs : HasSubst (A - 1) := HasSubst.of_constantCoeff_zero' hU
  have hsupp : (Function.support fun d =>
      coeff d (formalLogOuter R) • coeff N ((A - 1) ^ d)) ⊆ ↑(Finset.Icc 1 N) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_Icc, Set.mem_Icc]
    constructor
    · by_contra h1
      exact hd (by rw [coeff_formalLogOuter, if_pos (by omega), zero_smul])
    · by_contra h2
      exact hd (by rw [PositiveSeries.coeff_pow_eq_zero_of_lt hU (by omega), smul_zero])
  rw [formalLog, coeff_subst' hs, finsum_eq_finsetSum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_Icc] at hr
  rw [coeff_formalLogOuter, if_neg (by omega), smul_eq_mul]

/-- `def:weil-formal-derivative`.  The formal derivative
`D(∑ aₙ Tⁿ) = ∑ (n+1) aₙ₊₁ Tⁿ`, i.e. the map `PowerSeries.derivative R`. -/
def formalDerivative (A : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.derivative R A

/-- Coefficient formula for the formal derivative
(first half of `lemma:weil-formal-derivative-rules`). -/
theorem formalDerivative_coeff (A : R⟦X⟧) (n : ℕ) :
    coeff n (formalDerivative A) = ((n : R) + 1) * coeff (n + 1) A := by
  rw [formalDerivative, coeff_derivative, mul_comm]

/-- Product rule for the formal derivative
(second half of `lemma:weil-formal-derivative-rules`). -/
theorem formalDerivative_mul (A B : R⟦X⟧) :
    formalDerivative (A * B) = formalDerivative A * B + A * formalDerivative B := by
  simp only [formalDerivative]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

/-- `lemma:weil-formal-derivative-rules`, bundled as in the text. -/
theorem formalDerivative_rules (A B : R⟦X⟧) (n : ℕ) :
    coeff n (formalDerivative A) = ((n : R) + 1) * coeff (n + 1) A ∧
      formalDerivative (A * B) = formalDerivative A * B + A * formalDerivative B :=
  ⟨formalDerivative_coeff A n, formalDerivative_mul A B⟩

/-- `lemma:weil-formal-derivative-add`.  The formal derivative preserves
addition. -/
theorem formalDerivative_add (A B : R⟦X⟧) :
    formalDerivative (A + B) = formalDerivative A + formalDerivative B := by
  simp only [formalDerivative, map_add]

/-- The derivation law `D(1) = 0`, used repeatedly below. -/
theorem formalDerivative_one : formalDerivative (1 : R⟦X⟧) = 0 :=
  PowerSeries.derivative_one

/-- `lemma:weil-formal-log-outer-series-derivative`.  Derivative of the
universal outer logarithm. -/
theorem derivative_formalLogOuter :
    formalDerivative (formalLogOuter R) =
      PowerSeries.mk fun n => algebraMap ℚ R ((-1 : ℚ) ^ n) := by
  ext n
  rw [coeff_mk, formalDerivative_coeff, coeff_formalLogOuter, if_neg (Nat.succ_ne_zero n)]
  have hcast : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by
    rw [map_add, map_one, map_natCast]
  rw [hcast, ← map_mul]
  congr 1
  have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hp : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
  rw [hp]
  field_simp
  rw [pow_succ, pow_succ]
  ring

/-- `lemma:weil-formal-derivative-ext`.  Derivative and constant coefficient
determine a series. -/
theorem formalDerivative_ext {A B : R⟦X⟧}
    (hD : formalDerivative A = formalDerivative B)
    (hc : constantCoeff A = constantCoeff B) : A = B :=
  PowerSeries.derivative.ext hD hc

/-- `lemma:weil-formal-derivative-zero-constant-one`.  A normalized series
with zero derivative is one. -/
theorem eq_one_of_derivative_eq_zero_of_constantCoeff_eq_one {A : R⟦X⟧}
    (hD : formalDerivative A = 0) (hc : constantCoeff A = 1) : A = 1 :=
  formalDerivative_ext (by rw [hD, formalDerivative_one]) (by rw [hc, map_one])

/-- `def:weil-geometric-inverse`.  The geometric inverse of a one-series:
`GeomInv(A) = (∑ Xⁿ)|_{X = -(A-1)}`. -/
def geometricInverse (A : R⟦X⟧) : R⟦X⟧ :=
  subst (-(A - 1)) (PowerSeries.mk fun _ => (1 : R))

/-- Constant-coefficient certificate for the inner series of the geometric
inverse. -/
theorem constantCoeff_neg_sub_one_eq_zero {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    constantCoeff (-(A - 1)) = 0 := by
  rw [map_neg, constantCoeff_sub_one_eq_zero hA, neg_zero]

/-- `lemma:weil-geometric-inverse-coeff`.  Coefficient formula for the
geometric inverse. -/
theorem geometricInverse_coeff {A : R⟦X⟧} (hA : constantCoeff A = 1) (N : ℕ) :
    coeff N (geometricInverse A) =
      ∑ r ∈ Finset.range (N + 1), coeff N ((-(A - 1)) ^ r) := by
  have hU := constantCoeff_neg_sub_one_eq_zero hA
  have hs : HasSubst (-(A - 1)) := HasSubst.of_constantCoeff_zero' hU
  have hsupp : (Function.support fun d =>
      coeff d (PowerSeries.mk fun _ => (1 : R)) • coeff N ((-(A - 1)) ^ d)) ⊆
      ↑(Finset.range (N + 1)) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hdN
    exact hd (by rw [PositiveSeries.coeff_pow_eq_zero_of_lt hU (by omega), smul_zero])
  rw [geometricInverse, coeff_subst' hs, finsum_eq_finsetSum_of_support_subset _ hsupp]
  exact Finset.sum_congr rfl fun r _ => by rw [coeff_mk, one_smul]

/-- `lemma:weil-geometric-inverse-mul`.  The geometric inverse is a two-sided
inverse, obtained by applying `PowerSeries.substAlgHom` to the mathlib
identity `PowerSeries.mk_one_mul_one_sub_eq_one`. -/
theorem geometricInverse_mul {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    A * geometricInverse A = 1 ∧ geometricInverse A * A = 1 := by
  have hU := constantCoeff_neg_sub_one_eq_zero hA
  have hs : HasSubst (-(A - 1)) := HasSubst.of_constantCoeff_zero' hU
  have key : geometricInverse A * A = 1 := by
    have h0 := congrArg (substAlgHom (R := R) hs) (mk_one_mul_one_sub_eq_one R)
    simp only [map_mul, map_one, map_sub] at h0
    rw [substAlgHom_X] at h0
    have hmk : substAlgHom (R := R) hs (PowerSeries.mk 1) =
        geometricInverse A := by
      rw [coe_substAlgHom]
      rfl
    rw [hmk] at h0
    have hAred : (1 : R⟦X⟧) - -(A - 1) = A := by ring
    rwa [hAred] at h0
  exact ⟨by rw [mul_comm]; exact key, key⟩

/-- `lemma:weil-formal-geometric-inverse-constant`.  Constant coefficient of
the geometric inverse. -/
theorem formalGeometricInverse_constantCoeff {A : R⟦X⟧}
    (hA : constantCoeff A = 1) : constantCoeff (geometricInverse A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, geometricInverse_coeff hA]
  simp

/-- `lemma:weil-geometric-inverse-derivative`.  Derivative of the geometric
inverse. -/
theorem geometricInverse_derivative {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    formalDerivative (geometricInverse A) =
      -geometricInverse A ^ 2 * formalDerivative A := by
  have h1 := (geometricInverse_mul hA).1
  have hd := congrArg formalDerivative h1
  rw [formalDerivative_mul, formalDerivative_one] at hd
  linear_combination geometricInverse A * hd - formalDerivative (geometricInverse A) * h1

/-- `def:weil-geometric-comparison-series`.  The geometric comparison series
`Cmp(P, Q) = P · GeomInv(Q)`. -/
def geometricComparisonSeries (P Q : R⟦X⟧) : R⟦X⟧ :=
  P * geometricInverse Q

/-- `lemma:weil-geometric-comparison-derivative`.  Derivative of the geometric
comparison series. -/
theorem geometricComparisonSeries_derivative {P Q : R⟦X⟧}
    (hQ : constantCoeff Q = 1) :
    formalDerivative (geometricComparisonSeries P Q) =
      formalDerivative P * geometricInverse Q -
        P * geometricInverse Q ^ 2 * formalDerivative Q := by
  rw [geometricComparisonSeries, formalDerivative_mul, geometricInverse_derivative hQ]
  ring

/-- `lemma:weil-geometric-comparison-constant`.  Constant coefficient of a
normalized comparison series. -/
theorem geometricComparisonSeries_constantCoeff {P Q : R⟦X⟧}
    (hP : constantCoeff P = 1) (hQ : constantCoeff Q = 1) :
    constantCoeff (geometricComparisonSeries P Q) = 1 := by
  rw [geometricComparisonSeries, map_mul, hP,
    formalGeometricInverse_constantCoeff hQ, one_mul]

/-- `lemma:weil-geometric-comparison-derivative-zero`.  A common logarithmic
derivative kills the comparison. -/
theorem geometricComparisonSeries_derivative_eq_zero {H P Q : R⟦X⟧}
    (hQ : constantCoeff Q = 1)
    (hP' : formalDerivative P = H * P) (hQ' : formalDerivative Q = H * Q) :
    formalDerivative (geometricComparisonSeries P Q) = 0 := by
  rw [geometricComparisonSeries_derivative hQ]
  have hG := (geometricInverse_mul hQ).2
  linear_combination geometricInverse Q * hP' - P * geometricInverse Q ^ 2 * hQ' -
    H * P * geometricInverse Q * hG

/-- `lemma:weil-geometric-comparison-eq-one`.  A normalized common-ODE
comparison is one. -/
theorem geometricComparisonSeries_eq_one {H P Q : R⟦X⟧}
    (hP1 : constantCoeff P = 1) (hQ1 : constantCoeff Q = 1)
    (hP' : formalDerivative P = H * P) (hQ' : formalDerivative Q = H * Q) :
    geometricComparisonSeries P Q = 1 :=
  eq_one_of_derivative_eq_zero_of_constantCoeff_eq_one
    (geometricComparisonSeries_derivative_eq_zero hQ1 hP' hQ')
    (geometricComparisonSeries_constantCoeff hP1 hQ1)

/-- `lemma:weil-common-logarithmic-derivative-unique`.  Uniqueness for
normalized formal logarithmic ODEs. -/
theorem eq_of_same_logarithmicDerivative {H P Q : R⟦X⟧}
    (hP1 : constantCoeff P = 1) (hQ1 : constantCoeff Q = 1)
    (hP' : formalDerivative P = H * P) (hQ' : formalDerivative Q = H * Q) :
    P = Q := by
  have hc := geometricComparisonSeries_eq_one hP1 hQ1 hP' hQ'
  rw [geometricComparisonSeries] at hc
  have hG := (geometricInverse_mul hQ1).2
  linear_combination Q * hc - P * hG

/-- `lemma:weil-formal-exp-derivative`.  Chain rule for the formal
exponential. -/
theorem formalExp_derivative {U : R⟦X⟧} (hU : constantCoeff U = 0) :
    formalDerivative (formalExp U) = formalDerivative U * formalExp U := by
  have hs : HasSubst U := HasSubst.of_constantCoeff_zero' hU
  show PowerSeries.derivative R ((exp R).subst U) = _
  rw [derivative_subst hs, derivative_exp, mul_comm]
  rfl

/-- `lemma:weil-deriv-log-subst-eq-geometric-inverse`.  The substituted
derivative of the logarithm is the geometric inverse. -/
theorem subst_derivLog_eq_geometricInverse {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    (formalDerivative (formalLogOuter R)).subst (A - 1) = geometricInverse A := by
  have hU := constantCoeff_sub_one_eq_zero hA
  have hs : HasSubst (A - 1) := HasSubst.of_constantCoeff_zero' hU
  ext N
  have hsupp : (Function.support fun d =>
      coeff d (PowerSeries.mk fun n => algebraMap ℚ R ((-1 : ℚ) ^ n)) •
        coeff N ((A - 1) ^ d)) ⊆ ↑(Finset.range (N + 1)) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hdN
    exact hd (by rw [PositiveSeries.coeff_pow_eq_zero_of_lt hU (by omega), smul_zero])
  rw [derivative_formalLogOuter, coeff_subst' hs,
    finsum_eq_finsetSum_of_support_subset _ hsupp, geometricInverse_coeff hA]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : (-(A - 1)) ^ r = ((-1 : R) ^ r) • (A - 1) ^ r := by
    rw [← neg_one_smul R (A - 1), smul_pow]
  rw [coeff_mk, smul_eq_mul, h1, LinearMap.map_smul, smul_eq_mul,
    map_pow, map_neg, map_one]

/-- `lemma:weil-formal-log-derivative`.  Chain rule for the formal
logarithm. -/
theorem formalLog_derivative {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    formalDerivative (formalLog A) = formalDerivative A * geometricInverse A := by
  have hU := constantCoeff_sub_one_eq_zero hA
  have hs : HasSubst (A - 1) := HasSubst.of_constantCoeff_zero' hU
  have key := subst_derivLog_eq_geometricInverse hA
  simp only [formalDerivative] at key ⊢
  rw [formalLog, derivative_subst hs, key, map_sub, derivative_one, sub_zero, mul_comm]

/-- `lemma:weil-formal-exp-sum-derivative`.  Derivative of the exponential of
a sum. -/
theorem formalExp_sum_derivative {U V : R⟦X⟧}
    (hU : constantCoeff U = 0) (hV : constantCoeff V = 0) :
    formalDerivative (formalExp (U + V)) =
      (formalDerivative U + formalDerivative V) * formalExp (U + V) := by
  have hUV : constantCoeff (U + V) = 0 := by rw [map_add, hU, hV, add_zero]
  rw [formalExp_derivative hUV, formalDerivative_add]

/-- `lemma:weil-formal-exp-product-derivative`.  Derivative of a product of
two formal exponentials. -/
theorem formalExp_product_derivative {U V : R⟦X⟧}
    (hU : constantCoeff U = 0) (hV : constantCoeff V = 0) :
    formalDerivative (formalExp U * formalExp V) =
      (formalDerivative U + formalDerivative V) * (formalExp U * formalExp V) := by
  rw [formalDerivative_mul, formalExp_derivative hU, formalExp_derivative hV]
  ring

/-- `lemma:weil-formal-exp-add`.  The formal exponential converts sums to
products. -/
theorem formalExp_add {U V : R⟦X⟧}
    (hU : constantCoeff U = 0) (hV : constantCoeff V = 0) :
    formalExp (U + V) = formalExp U * formalExp V := by
  have hUV : constantCoeff (U + V) = 0 := by rw [map_add, hU, hV, add_zero]
  refine eq_of_same_logarithmicDerivative (H := formalDerivative U + formalDerivative V)
    (formalExp_constantCoeff hUV) ?_
    (formalExp_sum_derivative hU hV) (formalExp_product_derivative hU hV)
  rw [map_mul, formalExp_constantCoeff hU, formalExp_constantCoeff hV, mul_one]

/-- `lemma:weil-formal-log-exp`.  Logarithm after exponential. -/
theorem formalLog_formalExp {U : R⟦X⟧} (hU : constantCoeff U = 0) :
    formalLog (formalExp U) = U := by
  have hc := formalExp_constantCoeff hU
  refine formalDerivative_ext ?_ ?_
  · rw [formalLog_derivative hc, formalExp_derivative hU]
    have hG := (geometricInverse_mul hc).1
    linear_combination formalDerivative U * hG
  · rw [formalLog_constantCoeff hc, hU]

/-- `lemma:weil-formal-exp-logarithm-derivative`.  Derivative of the
exponential of a formal logarithm. -/
theorem formalExp_logarithm_derivative {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    formalDerivative (formalExp (formalLog A)) =
      (formalDerivative A * geometricInverse A) * formalExp (formalLog A) := by
  rw [formalExp_derivative (formalLog_constantCoeff hA), formalLog_derivative hA]

/-- `lemma:weil-one-series-logarithmic-ode`.  A one-series satisfies its
logarithmic ODE. -/
theorem oneSeries_logarithmicODE {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    formalDerivative A = (formalDerivative A * geometricInverse A) * A := by
  have hG := (geometricInverse_mul hA).2
  linear_combination -formalDerivative A * hG

/-- `lemma:weil-formal-exp-log`.  Exponential after logarithm. -/
theorem formalExp_formalLog {A : R⟦X⟧} (hA : constantCoeff A = 1) :
    formalExp (formalLog A) = A :=
  eq_of_same_logarithmicDerivative
    (formalExp_constantCoeff (formalLog_constantCoeff hA)) hA
    (formalExp_logarithm_derivative hA) (oneSeries_logarithmicODE hA)

/-- `prop:weil-formal-exp-log-inverse`.  Formal exponential and logarithm are
inverse bijections between `TR[[T]]` and `OneSeries(R)`. -/
def formalExpLogEquiv : PositiveSeries R ≃ OneSeries R where
  toFun U := ⟨formalExp (U : R⟦X⟧), formalExp_constantCoeff U.2⟩
  invFun A := ⟨formalLog (A : R⟦X⟧), formalLog_constantCoeff A.2⟩
  left_inv U := Subtype.ext (formalLog_formalExp U.2)
  right_inv A := Subtype.ext (formalExp_formalLog A.2)

/-- `lemma:weil-formal-log-mul`.  The formal logarithm converts a product to
a sum. -/
theorem formalLog_mul {A B : R⟦X⟧}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) :
    formalLog (A * B) = formalLog A + formalLog B := by
  have hLA := formalLog_constantCoeff hA
  have hLB := formalLog_constantCoeff hB
  have h := formalExp_add hLA hLB
  rw [formalExp_formalLog hA, formalExp_formalLog hB] at h
  calc formalLog (A * B)
      = formalLog (formalExp (formalLog A + formalLog B)) := by rw [h]
    _ = formalLog A + formalLog B :=
        formalLog_formalExp (by rw [map_add, hLA, hLB, add_zero])

end

end Weil
