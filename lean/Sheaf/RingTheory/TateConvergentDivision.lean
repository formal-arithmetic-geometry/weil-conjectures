module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.Groebner

/-!
# Bounded convergent division in Tate algebras

Source: agent auxiliary bounded-division lemma for BGR, Corollary 5.2.7/8; compare
Bosch, Lectures on Formal and Rigid Geometry (April 2008), §1.2, Theorem 8 proof,
and §1.3, Corollaries 7--9 (blueprint: lem-trf-tate-convergent-division).
The finite-list multivariate statement is an agent auxiliary lemma, not a verbatim
printed theorem of either reference.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- Bounded division by an arbitrary finite list of Gauss-norm-one restricted series.
The witnesses `β i` are precisely the largest graded lexicographic exponents attaining
the Gauss norm of `b i`; the order on exponents in the remainder condition is componentwise.
Source: the agent auxiliary multivariate bounded-division argument for BGR 5.2.7/8,
corroborated by Bosch, Lectures on Formal and Rigid Geometry (April 2008), §1.2,
Theorem 8 proof, pp. 12--13, and §1.3, Corollaries 7--9, pp. 20--21
(blueprint: lem-trf-tate-convergent-division).

Proof plan:
1. If the list is empty take `r = f`. With no variables and a nonempty list, divide
   by its first norm-one constant and set the remainder and other quotients to zero.
   Scalar multiplication has its exact Gauss-norm bound directly from the supremum.
2. Write `b i = H i + e i`, where `H i` consists of the finitely many norm-one
   coefficients. Restrictedness implies that the positive coefficient supremum is
   attained: maximize over the finite set above any fixed nonzero coefficient.
   It also gives a common `0 < c < 1` with Gauss norm of every `e i` at most `c`:
   use the finitely many coefficients of size at least `1/2`. The largest exponent
   of `H i` is `β i`. Its leading coefficient is a unit in the valuation subring.
   Graded lexicographic order is additive and well-founded, since bounded-degree
   exponent sets are finite.
3. Apply lem-trf-unit-leading-ring-polynomial-division, namely `MonomialOrder.div`,
   over that valuation subring to each monomial. Fix polynomial solutions
   `X^ν = ∑ i, A i ν * H i + B ν`, with all coefficients of size at most one and
   the support of `B ν` outside every componentwise multiple of `β i`.
4. For `h = ∑ ν, hν X^ν`, sum `hν * A i ν` and `hν * B ν` by total-degree
   truncations to define `Q i h` and `R h`. The tail norms are bounded by
   `sup_{|ν| > N} |hν|`, which tends to zero. By
   lem-trf-restricted-series-gauss-completion these limits exist, are linear and
   norm-nonincreasing, and satisfy `h = ∑ i, Q i h * H i + R h`.
   Coefficient evaluation is bounded by the Gauss norm, so `R h` has the required support.
5. Starting with `h₀ = f`, put `u i n = Q i hₙ`, `vₙ = R hₙ`, and
   `hₙ₊₁ = -∑ i, u i n * e i`. Then
   `hₙ = ∑ i, u i n * b i + vₙ + hₙ₊₁` and all new terms have norm at most
   `c^n * ‖f‖` by the ultrametric and submultiplicative Gauss estimates of
   lem-trf-restricted-series-gauss-completion.
6. Sum `u i n` and `vₙ` over `n`. Their tails are bounded by `c^N * ‖f‖`, hence
   completeness gives restricted-series limits `q i` and `r`. The finite identities
   telescope, and continuity of multiplication gives the asserted decomposition.
7. Every partial sum has Gauss norm at most that of `f`; the limit has the same
   bound by ultrametricity. Forbidden coefficients of every `vₙ` are zero, so
   continuity of coefficient evaluation gives the remainder condition for `r`.
   No Gröbner-basis hypothesis or uniqueness is used. -/
theorem exists_bounded_division
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (s t : ℕ)
    (b : Fin t → MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin s ↦ (1 : ℝ)))
    (hb : ∀ i : Fin t,
      MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin s ↦ 1) (b i).val = 1)
    (f : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin s ↦ (1 : ℝ))) :
    ∃ (β : Fin t → (Fin s →₀ ℕ))
      (q : Fin t → MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin s ↦ (1 : ℝ)))
      (r : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin s ↦ (1 : ℝ))),
      (∀ i : Fin t,
        MvPowerSeries.AchievesGaussNorm (norm : K → ℝ) (fun _ : Fin s ↦ 1)
          (b i).val (β i) ∧
        ∀ μ : Fin s →₀ ℕ,
          MvPowerSeries.AchievesGaussNorm (norm : K → ℝ) (fun _ : Fin s ↦ 1)
            (b i).val μ → toDegLex μ ≤ toDegLex (β i)) ∧
      f = (∑ i : Fin t, q i * b i) + r ∧
      (∀ i : Fin t,
        MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin s ↦ 1) (q i).val ≤
          MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin s ↦ 1) f.val) ∧
      MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin s ↦ 1) r.val ≤
        MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin s ↦ 1) f.val ∧
      (∀ ν : Fin s →₀ ℕ, MvPowerSeries.coeff ν r.val ≠ 0 →
        ∀ i : Fin t, ¬ β i ≤ ν) := by
  sorry

end RestrictedSeries
