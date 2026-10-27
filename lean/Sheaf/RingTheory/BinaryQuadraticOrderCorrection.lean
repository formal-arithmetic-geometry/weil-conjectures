module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-!
# Homogeneous corrections for a binary quadratic

Source: Stacks Project, curves.tex, Tag 0C49 (lemma-nodal-algebraic), proof of
(2) implies (3), polar correction and its higher-order induction, with fixed series f.
(blueprint: lem-trf-binary-quadratic-order-correction)
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- A nondegenerate binary quadratic admits a degree-r coordinate correction raising
an approximation's error from order r+1 to order r+2, in every characteristic.
The equality binders specify the quadratic Q, the variable ideal p, and the polynomial
homogeneous part H. The final universally quantified x', y' are the specified corrected
coordinates, not additional choices or hypotheses on the original approximation.

Source: Stacks Project, curves.tex, Tag 0C49 (lemma-nodal-algebraic), proof of
(2) implies (3), polar correction and its higher-order induction, with fixed series f.
(blueprint: lem-trf-binary-quadratic-order-correction)

Proof:
1. Apply power_series_mem_combined_ideal_pow_iff with base ideal zero and two variables
   (lem-weil-pbc-power-series-combined-ideal-coefficients). Membership in p^n means
   vanishing of coefficients below degree n. Therefore E-H lies in p^(r+2), where
   E=f-Q(x,y); the degree-(r+1) part is a polynomial since there are finitely many
   binary monomials of that degree.
2. Write H=uP+vR by assigning each monomial divisible by u to uP and the remaining
   monomial to vR. Both P and R are homogeneous of degree r. Put D=4ac-b^2 and take
   A=D^(-1)(2cP-bR), B=D^(-1)(-bP+2aR). Then 2aA+bB=P and bA+2cB=R, so
   H=(2au+bv)A+(bu+2cv)B. Only the nonzero scalar D is inverted.
3. Since x-u and y-v lie in p^2, both x,y lie in p. Telescoping powers gives
   x^i*y^j-u^i*v^j in p^(r+1) for i+j=r, including zero exponents. Hence
   delta=A(x,y), epsilon=B(x,y) lie in p^r, while delta-A(u,v) and epsilon-B(u,v)
   lie in p^(r+1).
4. Put x'=x+delta and y'=y+epsilon. Their increments lie in p^r, and r>=2 preserves
   the identity linear part. The polar forms M1=2ax+by, M2=bx+2cy lie in p and differ
   from L1=2au+bv, L2=bu+2cv by p^2. Multiplication of ideal powers then gives
   M1*delta+M2*epsilon-H in p^(r+2).
5. Expand Q(x',y')-Q(x,y)=M1*delta+M2*epsilon+a*delta^2+b*delta*epsilon+c*epsilon^2.
   The last terms lie in p^(2r), contained in p^(r+2). Subtracting this congruence
   from E-H gives the new error in p^(r+2). No division by 2 or r is used.
-/
theorem exists_binary_quadratic_order_correction
    (F : Type u) [Field F] (a b c : F) (hdisc : b ^ 2 - 4 * a * c ≠ 0)
    (Q : MvPolynomial (Fin 2) F)
    (hQ : Q = MvPolynomial.C a * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C b * MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.C c * MvPolynomial.X 1 ^ 2)
    (p : Ideal (MvPowerSeries (Fin 2) F))
    (hp : p = Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) F)))
    (r : ℕ) (hr : 2 ≤ r) (f x y : MvPowerSeries (Fin 2) F)
    (hx : x - X 0 ∈ p ^ 2) (hy : y - X 1 ∈ p ^ 2)
    (hE : f - MvPolynomial.aeval ![x, y] Q ∈ p ^ (r + 1))
    (H : MvPolynomial (Fin 2) F)
    (hH : (H : MvPowerSeries (Fin 2) F) =
      homogeneousComponent (r + 1) (f - MvPolynomial.aeval ![x, y] Q)) :
    ∃ A B : MvPolynomial (Fin 2) F,
      A.IsHomogeneous r ∧ B.IsHomogeneous r ∧
      (H : MvPowerSeries (Fin 2) F) =
        ((2 * a) • X 0 + b • X 1) * (A : MvPowerSeries (Fin 2) F) +
        (b • X 0 + (2 * c) • X 1) * (B : MvPowerSeries (Fin 2) F) ∧
      ∀ x' y' : MvPowerSeries (Fin 2) F,
        x' = x + MvPolynomial.aeval ![x, y] A →
        y' = y + MvPolynomial.aeval ![x, y] B →
        x' - x ∈ p ^ r ∧ y' - y ∈ p ^ r ∧
        x' - X 0 ∈ p ^ 2 ∧ y' - X 1 ∈ p ^ 2 ∧
        MvPolynomial.aeval ![x', y'] Q - MvPolynomial.aeval ![x, y] Q -
          (H : MvPowerSeries (Fin 2) F) ∈ p ^ (r + 2) ∧
        f - MvPolynomial.aeval ![x', y'] Q ∈ p ^ (r + 2) := by
  sorry

end MvPowerSeries
