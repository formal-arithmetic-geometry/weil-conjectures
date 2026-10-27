module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Kaehler.Polynomial
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-!
# Adic gradient control and finite-level differentiation of power series

Source: literature/stacks-project/algebra.tex, Tags 02HQ
(lemma-differential-mod-power-ideal) and 00RX (lemma-differentials-polynomial-ring),
with the explicit total-degree coefficient and polynomial approximation argument.
(blueprint: lem-trf-power-series-adic-gradient-control)
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- Formal partial derivatives lower the variable-ideal filtration by one, agree with
polynomial derivatives, and compute universal differentials in each finite quotient.
The truncation at total degree less than `r + 1` approximates a series to that precision
and its derivatives to precision `r`, over a field of arbitrary characteristic.

Source: literature/stacks-project/algebra.tex, Tags 02HQ
(lemma-differential-mod-power-ideal) and 00RX (lemma-differentials-polynomial-ring);
explicit coefficient/truncation argument extracted from the ambient formal-series
comparison in the proof of lem-trf-local-term-locality.
(blueprint: lem-trf-power-series-adic-gradient-control)

Proof:
1. Apply `power_series_mem_combined_ideal_pow_iff`
   (lem-weil-pbc-power-series-combined-ideal-coefficients) with base ideal zero.
   Membership in the kth variable-ideal power is vanishing of coefficients below
   degree k. If s ≥ 2 and degree E < s-1, then degree (E+e_i) < s. The coefficient
   formula for `pderiv` (def-trf-formal-power-series-partial-derivative) makes the
   coefficient at E vanish. If s = 1 the target ideal power is the whole ring.
2. The monomial formula for `MvPolynomial.pderiv`
   (def-weil-pbc-polynomial-partial-derivative) gives precisely the same coefficients
   as the series derivative, proving compatibility. The polynomial embedding sends
   every variable generator into the series variable ideal and hence sends its rth
   power into the rth series ideal power. Step 1 gives each gradient coordinate bound.
3. Only finitely many multi-indices have degree less than r+1. The polynomial
   `truncTotal (r+1) h` has exactly the coefficients of h in those degrees. The same
   coefficient criterion puts its tail in the (r+1)st power. Additivity, Step 1, and
   Step 2 put every derivative difference in the rth power.
4. Compose the polynomial embedding and quotient map with the universal derivation
   of Q_r. Its universal factorization through polynomial Kahler differentials
   (def-weil-pbc-kahler-differentials) sends dX_i to d of the quotient of X_i.
   Apply it to the polynomial basis formula
   (lem-weil-pbc-polynomial-ring-kahler-basis-any-variables) for the truncation.
   Step 3 identifies its quotient and all derivative quotients with those of h,
   giving the asserted finite sum. For n = 0 all series are constants, the variable
   ideals vanish, and both the relative differential and empty sum are zero.
   Integer factors are multiplied in F throughout; none are inverted.
-/
theorem adic_gradient_control (F : Type u) [Field F] (n : ℕ) :
    (∀ s : ℕ, 1 ≤ s → ∀ f : MvPowerSeries (Fin n) F,
      f ∈ (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ s →
      ∀ i : Fin n, pderiv F i f ∈
        (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ (s - 1)) ∧
    (∀ r : ℕ, 1 ≤ r → ∀ g : MvPolynomial (Fin n) F,
      g ∈ (Ideal.span (Set.range
        (MvPolynomial.X : Fin n → MvPolynomial (Fin n) F))) ^ r →
      ∀ i : Fin n,
        ((MvPolynomial.pderiv i g : MvPowerSeries (Fin n) F) ∈
          (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ (r - 1)) ∧
        (MvPolynomial.pderiv i g : MvPowerSeries (Fin n) F) =
          pderiv F i (g : MvPowerSeries (Fin n) F)) ∧
    (∀ (h : MvPowerSeries (Fin n) F) (r : ℕ), 1 ≤ r →
      (h - (truncTotal (r + 1) h : MvPowerSeries (Fin n) F) ∈
        (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ (r + 1)) ∧
      (∀ i : Fin n,
        pderiv F i h - pderiv F i (truncTotal (r + 1) h : MvPowerSeries (Fin n) F) ∈
          (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ r) ∧
      KaehlerDifferential.D F
          (MvPowerSeries (Fin n) F ⧸
            (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ r)
          (Ideal.Quotient.mk _ h) =
        ∑ i : Fin n, Ideal.Quotient.mk
            ((Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ r)
            (pderiv F i h) •
          KaehlerDifferential.D F
            (MvPowerSeries (Fin n) F ⧸
              (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ^ r)
            (Ideal.Quotient.mk _ (X i))) := by
  sorry

end MvPowerSeries
