module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Algebra.Polynomial.Splits

/-! # Root-product rigidity over the p-adic numbers

Source: Milne, Abelian Varieties, Chapter I, Lemma 10.21, printed p.51
(blueprint: lem-sfb-padic-resultant-rigidity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace Polynomial

/-- Two monic polynomials of the same degree over the p-adic numbers coincide if every
integer polynomial has root products of equal absolute value. The equalities `ha` and `hb`
specify complete root lists, including multiplicity. The absolute value is any extension
of the normalized p-adic absolute value to the chosen algebraic closure.

Source: Milne, Abelian Varieties, Chapter I, Lemma 10.21 and proof, printed p.51
(blueprint: lem-sfb-padic-resultant-rigidity).

Proof plan:
1. For degree zero, monicity gives `P = Q = 1`. Otherwise clear the denominators of a
rational test polynomial using a nonzero integer `N`. The two products acquire the same
positive factor `|N|^d`, which cancels. This uses def-weil-polynomial-ring and
def-weil-l-adic-numbers.
2. Approximate each coefficient of a p-adic test polynomial by rational numbers, using
the density clause of lem-sfb-padic-minpoly-normed-separation. The extended absolute value
is nonarchimedean by lem-sfb-ultrametric-criterion-natural-norms, since the norms of all
natural numbers are at most one. For a root `c` and a test polynomial of degree at most
`s`, coefficient errors below `1/n` bound the evaluation error by
`(1/n) * max (1, |c|)^s`. Thus evaluations converge. The telescoping identity for the
difference of two finite products gives convergence of their products, and the reverse
triangle inequality gives convergence of their absolute values. Pass to the limit to
obtain the test identity for every p-adic polynomial.
3. For any element `alpha` of the closure, its minimal polynomial has positive degree
`m`, by lem-sfb-padic-minpoly-normed-separation. Apply step 2 to this polynomial and
lem-sfb-padic-minpoly-root-product to `P` and `Q`. It follows that
`|P(alpha)|^m = |Q(alpha)|^m`. Injectivity of positive powers on nonnegative real numbers
gives `|P(alpha)| = |Q(alpha)|`.
4. Fix a root `x` in either list, of multiplicities `e` and `f`. Monic factorization
(lem-weil-alg-closed-linear-factorization) and the strong triangle inequality show that,
for all sufficiently large `n`, evaluation at `x + ell^n` has absolute values
`C_P * ell^(-n*e)` and `C_Q * ell^(-n*f)`, with positive constants `C_P` and `C_Q`
coming from the other roots. Choose the perturbation smaller than every nonzero distance
to a listed root; an empty set of such distances permits radius one. Compare step 3 at
two successive `n` and cancel the positive constants. Since `ell` is prime, `ell >= 2`,
so `e = f`. The complete root multisets coincide, hence so do the monic factorizations.
Injectivity of the field inclusion gives equality over the base. Empty products are one.
-/
theorem eq_of_padic_root_product_abs_eq
    (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (v : AbsoluteValue Ω ℝ)
    (hv : ∀ x : ℚ_[ell], v (algebraMap ℚ_[ell] Ω x) = ‖x‖)
    (d : ℕ) (P Q : Polynomial ℚ_[ell])
    (hP : P.Monic) (hQ : Q.Monic) (hdegP : P.natDegree = d) (hdegQ : Q.natDegree = d)
    (a b : Fin d → Ω)
    (ha : (↑(List.ofFn a) : Multiset Ω) = (P.map (algebraMap ℚ_[ell] Ω)).roots)
    (hb : (↑(List.ofFn b) : Multiset Ω) = (Q.map (algebraMap ℚ_[ell] Ω)).roots)
    (h : ∀ F : Polynomial ℤ,
      v (∏ i : Fin d, F.eval₂ (Int.castRingHom Ω) (a i)) =
        v (∏ i : Fin d, F.eval₂ (Int.castRingHom Ω) (b i))) :
    P = Q := by
  sorry

end Polynomial
