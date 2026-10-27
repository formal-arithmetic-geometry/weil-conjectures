module

public import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Data.Nat.Choose.Sum

/-! # Linear substitution for divided-power multinomial expressions

Source: Stacks Project, Tag 07H1 (`lemma-gamma-extends`), the matrix-substitution
identity in the flat-case proof (blueprint: lem-sfb-pd-linear-substitution).
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace DividedPowers

/-- A matrix over the source ring can be moved from the coefficients to the ideal tuple
in the divided-power multinomial expression over an arbitrary target ring.

Source: Stacks Project, Tag 07H1 (`lemma-gamma-extends`), the matrix-substitution
identity preceding the common-refinement argument
(blueprint: lem-sfb-pd-linear-substitution).

A member `e` of `Finset.univ.sym n` is a multiset of `n` indices. Its multiplicities
`Multiset.count i e` give exactly one exponent tuple of total degree `n`, and every
such tuple occurs exactly once. Thus the two finite sums below are precisely the
expressions `P_n(x; b)` and `P_n(y; c)` in the node, with the displayed substitutions
for `b` and `y` expanded. No divided powers on the target ring are used.

Proof plan:
1. On arrays indexed by `0, ..., n`, define finite convolution by summing over
   `p + q = m`. Commutativity and associativity follow by reindexing pairs and
   triples; the unit has entry one at zero and zero elsewhere. The degree-`m`
   entry of a finite convolution product is the sum over exponent tuples of
   total degree `m` of the corresponding products, also for an empty product.
2. Write `E(z; t)_m = t ^ m * f (γ.dpow m z)`. The scalar axiom at scalar zero
   gives `γ.dpow m 0 = 0` for positive `m`, while the zeroth operation on the
   ideal is one. Consequently `E(0; t)` and `E(z; 0)` are the convolution unit.
3. Apply the binomial theorem (lem-pur-commutative-ring-binomial-expansion) and
   the divided-power product axiom to obtain `E(z; t + u) = E(z; t) * E(z; u)`.
   The unital ring map preserves the binomial coefficients. Zero indices use
   the zeroth operation and the endpoint coefficient one.
4. The addition and scalar axioms give `E(z + w; t) = E(z; t) * E(w; t)` and
   `E(a * z; t) = E(z; f(a) * t)`. Ideal membership is preserved by these sums
   and scalar multiples; these formulas also hold in degree zero.
5. Iterate steps 3 and 4 over the two finite tuples, using step 2 for empty
   sums. Rewrite the convolution product over `i` as the product over `(i,j)`
   of `E(a i j * x i; c j)`. Reorder these factors by step 1 and then combine
   each column to obtain the product over `j` of `E(∑ i, a i j * x i; c j)`.
   Taking the degree-`n` entries gives the stated identity, including empty
   tuples, zero coefficients, and the zero ideal.
-/
theorem dpow_multinomial_linear_substitution
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (γ : DividedPowers I)
    (r s : ℕ) (x : Fin r → A) (hx : ∀ i : Fin r, x i ∈ I)
    (a : Fin r → Fin s → A) (c : Fin s → B) (n : ℕ) :
    (∑ e ∈ (Finset.univ : Finset (Fin r)).sym n,
      ∏ i : Fin r,
        (∑ j : Fin s, f (a i j) * c j) ^ Multiset.count i e *
          f (γ.dpow (Multiset.count i e) (x i))) =
    ∑ d ∈ (Finset.univ : Finset (Fin s)).sym n,
      ∏ j : Fin s,
        c j ^ Multiset.count j d *
          f (γ.dpow (Multiset.count j d) (∑ i : Fin r, a i j * x i)) := by
  sorry

end DividedPowers
