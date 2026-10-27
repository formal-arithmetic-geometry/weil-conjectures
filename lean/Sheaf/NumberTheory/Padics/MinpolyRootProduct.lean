module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.NumberTheory.Padics.PadicNumbers

import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Normal.Basic

/-! # Minimal-polynomial root-product absolute value

Source: Milne, Abelian Varieties, Chapter I, proof of Lemma 10.21, printed p.51,
the two displayed minimal-polynomial root-product identities
(blueprint: lem-sfb-padic-minpoly-root-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace Polynomial

/-- The absolute value of the product of minimal-polynomial evaluations on a complete root
list of a monic polynomial `H` equals the absolute value of `H` at the algebraic element,
raised to the degree of its minimal polynomial. The list records multiplicities, and its
length may be zero. The absolute value is any extension of the normalized p-adic one.

Source: Milne, Abelian Varieties, Chapter I, proof of Lemma 10.21, printed p.51,
the displayed formulas for the products of `F(a_i)` and `F(b_i)`
(blueprint: lem-sfb-padic-minpoly-root-product).

Proof plan:
1. The minimal polynomial `f` is monic, by def-weil-pbc-separable-algebraic-extension.
Factor it and `H` into linear factors in the algebraic closure, listing all roots with
multiplicity, by lem-weil-alg-closed-linear-factorization. Write the roots of `f` as
`alpha_j`, with `m = f.natDegree` factors; `H` has the given `r` factors.
2. The algebraic closure is algebraic and normal over the base. By
lem-weil-pbc-normal-extension-conjugate-by-automorphism, each `alpha_j` is `sigma_j alpha`
for a base-field automorphism `sigma_j` of the closure.
3. The p-adic base is complete, nontrivially valued and nonarchimedean, by
def-weil-l-adic-numbers. Both `v` and `v` composed with `sigma_j` extend its absolute
value. The uniqueness lemma lem-sfb-algebraic-absolute-value-unique therefore gives
`v (sigma_j z) = v z`. Since `sigma_j` fixes the coefficients of `H`, evaluation commutes
with it, hence `v (H(alpha_j)) = v (H(alpha))`.
4. Rearrange the finite double product to obtain
`prod_i f(c_i) = (-1)^(r*m) * prod_j H(alpha_j)`. Multiplicativity of the absolute
value and `v (-1) = 1` give the asserted power. This uses no cancellation of evaluations,
so zero evaluations are included. If `r = 0`, monicity gives `H = 1` and both sides are one.
-/
theorem abs_prod_minpoly_eq_aeval_pow_natDegree
    (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (v : AbsoluteValue Ω ℝ)
    (hv : ∀ x : ℚ_[ell], v (algebraMap ℚ_[ell] Ω x) = ‖x‖)
    (r : ℕ) (H : Polynomial ℚ_[ell]) (hH : H.Monic) (hdeg : H.natDegree = r)
    (c : Fin r → Ω)
    (hc : (↑(List.ofFn c) : Multiset Ω) = (H.map (algebraMap ℚ_[ell] Ω)).roots)
    (alpha : Ω) :
    v (∏ i : Fin r, aeval (c i) (minpoly ℚ_[ell] alpha)) =
      v (aeval alpha H) ^ (minpoly ℚ_[ell] alpha).natDegree := by
  sorry

end Polynomial
