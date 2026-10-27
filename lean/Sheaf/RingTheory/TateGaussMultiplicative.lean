module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# Multiplicativity of the Tate Gauss norm

Source: Bosch, Lectures on Formal and Rigid Geometry (2008), Section 1.2,
Gauss-norm discussion preceding Proposition 3, printed pp. 8--9
(blueprint: lem-trf-tate-gauss-multiplicative).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- The coefficient supremum norm of restricted series is multiplicative for the Cauchy product.
No completeness or nontriviality of the absolute value is required, and zero variables and
zero factors are included.

Source: Bosch, Lectures on Formal and Rigid Geometry (2008), Section 1.2,
Gauss-norm discussion preceding Proposition 3, printed pp. 8--9
(blueprint: lem-trf-tate-gauss-multiplicative).

Proof plan:
1. By def-trf-restricted-series-presentation, coefficients tend to zero in the cofinite filter.
The product coefficient at an index is the finite sum over its antidiagonal. If either factor
is zero, all product coefficients are zero, giving the equality immediately.
2. Otherwise choose a nonzero coefficient of absolute value t > 0 in each factor. Only finitely
many coefficients have absolute value at least t. The maximum on this finite nonempty set is
the supremum over all coefficients; the set of indices attaining it is finite and nonempty.
Write A and B for the two positive Gauss norms.
3. Every summand in every Cauchy coefficient has absolute value at most A * B. Apply the first
clause of lem-trf-nonarchimedean-finite-sums to obtain the same bound on each coefficient and
therefore on the Gauss norm of the product. These bounds also justify the real suprema.
4. Choose the lexicographically largest indices i and j attaining A and B. If u + v = i + j
and both u and v attain the respective maxima, maximality gives u <= i and v <= j. At the
first coordinate where u < i, the sum equation would force v > j. Thus u = i and v = j.
Every other antidiagonal pair has product absolute value strictly less than A * B.
5. Apply the second clause of lem-trf-nonarchimedean-finite-sums to the coefficient at i + j.
Its absolute value is A * B, giving the reverse inequality. With zero variables there is only
the empty multi-index. For a trivial absolute value restricted series have finite support,
so the same argument applies. No infinite coefficient sum or completeness is used. -/
theorem gaussNorm_mul (K : Type u) [NormedField K] [IsUltrametricDist K] (r : ℕ)
    (f g : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) :
    MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1) (f * g).val =
      MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1) f.val *
        MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1) g.val := by
  sorry

end RestrictedSeries
