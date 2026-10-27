module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # Characteristic polynomial of a multiplicative polynomial norm

Source: Milne, Abelian Varieties, Chapter I, Lemma 10.22, printed p.51, with
normalization and homogeneity as in Proposition 10.13 and Theorem 10.9, pp.47–48
(blueprint: lem-sfb-multiplicative-polynomial-norm).

The sign convention is `δ(t • 1 - u)`, giving a monic polynomial and a root
product identity without an undetermined sign. The integral-coefficient clause
is the general polynomial-norm version of Theorem 10.9.
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace Algebra

/-- A normalized multiplicative homogeneous rational polynomial function has a unique
monic characteristic polynomial, a root product formula, and integral coefficients
on elements annihilated by monic integer polynomials.

Source: Milne, Abelian Varieties, Chapter I, Lemma 10.22, printed p.51;
Proposition 10.13 and Theorem 10.9, printed pp.47–48
(blueprint: lem-sfb-multiplicative-polynomial-norm).

Proof plan:
1. Choose the basis `b` and representing polynomial `D`. Substitute the coordinates
   of `X • 1 - u` into `D`. Homogeneity bounds the degree by `d`, and the coefficient
   of `X^d` is `D(b.repr 1) = δ 1 = 1`. This gives monicity and degree `d`.
   Any other representing polynomial agrees at every rational number, so equals
   this one by lem-trf-polynomial-infinite-evaluation-identity.
2. Write multiplication in basis coordinates using rational structure constants.
   Multiplicativity says that `D(m(Z,W)) - D(Z)D(W)` vanishes on all rational tuples.
   Polynomial determination over an infinite field, the last assertion of
   lem-sfb-bounded-line-polynomial-interpolation, makes it the zero polynomial.
   Over any extension field use the same structure constants and polynomial `D`.
   Associativity and the unit equations persist, and evaluation of the zero
   identity proves multiplicativity of the extended function. Homogeneity gives
   δ_K(c x) = c^d δ_K(x), δ_K(c • 1) = c^d and δ_K(0) = 0 since `d > 0`.
3. Pass from the splitting field `L` to an algebraic closure `K`. Factor nonzero
   `F` as `c ∏ (T - b_j)` by lem-weil-alg-closed-linear-factorization. The factors
   evaluated at `u` commute because scalars are central and all factors are
   polynomials in the same element, even when the algebra is not commutative.
4. Multiplicativity gives δ_K(F(u)) = c^d (-1)^(d m) ∏ P(b_j). Expanding
   P(b_j) = ∏ (b_j - a_i) and reversing all `d m` differences cancels the sign,
   leaving ∏ F(a_i). Injectivity of `L → K` descends the equality to `L`.
   Nonzero constants use empty products; `F = 0` follows from δ_K(0) = 0 and `d > 0`.
5. If monic `H` over the integers annihilates `u`, every root `a` of `P` in an
   algebraic closure of the rationals is a root of `H`. Indeed,
   H(T) - H(a) = (T - a) Q(T). If H(a) ≠ 0, evaluation at `u` gives a right
   inverse for `u - a • 1`. Applying δ_K gives 0 = 1 since
   δ_K(u - a • 1) = (-1)^d P(a) = 0. Thus H(a) = 0.
6. If a root occurs `r` times in `P` and `s` times in `H`, then `r ≤ d s`:
   for `r > 0`, step 5 gives `s ≥ 1`, while `r ≤ d`. Multiplying the missing
   linear factors shows `P ∣ H^d` over the algebraic closure, including repeated
   roots. Descend divisibility to the rationals using
   lem-sfb-polynomial-divisibility-field-extension. Both `P` and `H^d` are monic,
   so lem-weil-monic-divisor-integral gives integer coefficients of `P`.
-/
theorem exists_characteristicPolynomial_of_multiplicative_homogeneous
    (E : Type u) [Ring E] [Algebra ℚ E] [Nontrivial E] [FiniteDimensional ℚ E]
    (d : ℕ) (hd : 0 < d) (δ : E → ℚ)
    (h_one : δ 1 = 1) (h_mul : ∀ x y : E, δ (x * y) = δ x * δ y)
    (h_poly : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ E)
        (D : MvPolynomial (Fin n) ℚ),
      D.IsHomogeneous d ∧ ∀ x : E, δ x = MvPolynomial.eval (b.repr x) D)
    (u : E) :
    ∃ P : Polynomial ℚ,
      P.Monic ∧ P.natDegree = d ∧
      (∀ t : ℚ, P.eval t = δ (t • (1 : E) - u)) ∧
      (∀ Q : Polynomial ℚ,
        (∀ t : ℚ, Q.eval t = δ (t • (1 : E) - u)) → Q = P) ∧
      (∀ (L : Type v) [Field L] [Algebra ℚ L] (a : Fin d → L),
        P.map (algebraMap ℚ L) =
          ∏ i : Fin d, (Polynomial.X - Polynomial.C (a i)) →
        ∀ F : Polynomial ℚ,
          algebraMap ℚ L (δ (Polynomial.aeval u F)) =
            ∏ i : Fin d, Polynomial.aeval (a i) F) ∧
      ((∃ H : Polynomial ℤ,
          H.Monic ∧ Polynomial.eval₂ (Int.castRingHom E) u H = 0) →
        ∀ k : ℕ, ∃ z : ℤ, P.coeff k = (z : ℚ)) := by
  sorry

end Algebra
