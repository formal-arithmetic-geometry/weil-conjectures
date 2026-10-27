module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.NumberTheory.Niven

/-!
# Algebraic-integer congruence rigidity for roots of unity

Source: Milne, Abelian Varieties, Chapter I, Lemma 14.5, printed p.63 (PDF p.69).
(blueprint: lem-sfb-algebraic-integer-root-unity-congruence)
-/

@[expose] public section

universe u

/-- A root of unity of the form `1 + n * α`, where `α` is an algebraic integer and the
integer `n` is at least three, is one. Source: Milne, Abelian Varieties, Chapter I,
Lemma 14.5, printed p.63 (PDF p.69).
(blueprint: lem-sfb-algebraic-integer-root-unity-congruence)

Proof:
1. Suppose `ζ ≠ 1`. Since the positive integer `r` satisfies `ζ ^ r = 1`, the least
   positive order `m` of `ζ` exists and is greater than one. Choose a prime `p` dividing
   `m`, set `s = m / p` and `η = ζ ^ s`. If `η ^ j = 1` for `1 ≤ j < p`, then
   `ζ ^ (s * j) = 1` with `0 < s * j < m`, contradicting minimality. Thus `η` has order `p`.
2. Expand `(1 + n * α) ^ s` and put
   `β = ∑ j = 1, ..., s, choose s j * n ^ (j - 1) * α ^ j`.
   Then `η = 1 + n * β`. Integral elements form a subring containing the integers
   (`def-weil-pbc-integral-closure`), so `β` is integral. Since `n ≠ 0`, the equality
   `β = (η - 1) / n` places it in `E = ℚ(η)`. Its monic integer equation holds in `E`
   because the inclusion into `K` is injective.
3. By `lem-sfb-prime-cyclotomic-degree-norm`, the extension `E/ℚ` has degree `p - 1`
   and `N(η - 1) = (-1) ^ (p - 1) * p`.
4. By `lem-sfb-field-norm-preserves-integrality`, `N(β)` is an algebraic integer in `ℚ`.
   The rational-integrality criterion `lem-weil-rational-algebraic-integer` gives an
   integer `b` with `N(β) = b`.
5. Apply multiplicativity and the scalar formula from `lem-sfb-finite-field-norm-minpoly`
   to `η - 1 = n * β`: `(-1) ^ (p - 1) * p = n ^ (p - 1) * b`. Injectivity of the
   integer inclusion into `ℚ` makes this an integer equality. Thus `n ^ (p - 1)` divides
   `p`, hence `n` divides `p`. Primality and `n ≥ 3` force `n = p ≥ 3`. Now `p - 1 ≥ 2`,
   so `p ^ 2` divides `p`, impossible. This contradiction gives `ζ = 1`. -/
theorem eq_one_of_isIntegral_root_unity_congruence
    {K : Type u} [Field K] [CharZero K] {ζ α : K} (hα : IsIntegral ℤ α)
    (n r : ℤ) (hn : 3 ≤ n) (hr : 1 ≤ r) (hζ : ζ ^ r = 1)
    (hcongr : ζ = 1 + (n : K) * α) : ζ = 1 := by
  sorry
