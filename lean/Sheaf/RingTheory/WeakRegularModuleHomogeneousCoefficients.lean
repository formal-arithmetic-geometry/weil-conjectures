/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Homogeneous coefficients for a weakly regular module sequence

Source: Stacks Project, Algebra, Tag 00LN, part (2) and its proof, together with
Tag 061N, equation-quasi-regular
(blueprint: lem-trf-weak-regular-module-homogeneous-coefficients).

Only injectivity on the successive module quotients is assumed. The module may
be zero and the parameter list may be empty. The finite set
`Finset.Nat.antidiagonalTuple s n` indexes exactly the natural multi-indices of
length `s` and total degree `n`.
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence.IsWeaklyRegular

/-- A degree-`n` monomial sum in the next power of the parameter ideal has every
module coefficient in the parameter ideal, for a weakly regular sequence.

Source: Stacks Project, Algebra, Tag 00LN, part (2), and Tag 061N,
equation-quasi-regular. The proof of 00LN uses no nonvanishing condition
(blueprint: lem-trf-weak-regular-module-homogeneous-coefficients).

Proof (the two definition inputs are `def-weil-pbc-regular-sequence` and
`def-weil-pbc-algebra-hom-quotient`):
1. For any finitely generated ideal H = (z), expand products of generators to
   obtain H^d N as the sum of z^beta N over degree-d multi-indices beta. In
   particular every element of H^(d+1) N is a degree-d monomial sum with
   coefficients in HN. For d = 0 this is N, including for an empty list.
2. Induct on the list length s, simultaneously for all degrees. At s = 0,
   J = 0. For n = 0 the premise puts the unique coefficient in zero; for n > 0
   there are no multi-indices. Assume the criterion for every shorter list.
3. For a sum v in J^(n+1) N, expand v as in step 1 with coefficients b_alpha
   in JN. Subtract these coefficients. It suffices to handle zero relations,
   since adding b_alpha back preserves membership in JN.
4. Write z for the prefix, K = (z), and t for the last parameter. The prefix
   is weakly regular. Injectivity of t on N/KN implies that t^l a in KN
   forces a in KN, by repeated cancellation. Also KN and tN lie in JN.
5. For fixed n, induct on l from 0 to n for zero relations of the form
   sum_(e=0)^l t^e sum_(|beta|=n-e) z^beta a_(beta,e) = 0.
   At l = 0 use the length induction on z in degree n: the zero prefix sum
   is in K^(n+1) N, so its coefficients are in KN and hence in JN.
6. For l > 0, terms with e < l lie in K^(n-l+1) N. Consequently the top
   prefix sum with coefficients t^l a_(beta,l) lies in K^(n-l+1) N.
   The length induction in degree n-l puts those coefficients in KN.
   Step 4 cancels t^l on N/KN, giving a_(beta,l) in KN.
7. Expand each top coefficient as sum_i z_i u_(beta,i), and collect terms
   with gamma = beta + epsilon_i into coefficients b_gamma. This raises
   the prefix degree by one. Replace a_(gamma,l-1) by
   a_(gamma,l-1) + t b_gamma. The original relation becomes a relation with
   upper exponent l-1. The inner induction puts its coefficients in JN;
   subtract t b_gamma to recover the original coefficients there. The top
   coefficients already lie in KN. Empty prefixes give empty sums here.
8. Splitting a full multi-index into its prefix and last exponent identifies
   every degree-n relation with the case l = n. Apply the inner induction
   and then step 3. This completes the length induction. All operations
   remain valid for N = 0; when JN = N the conclusion is automatic.
-/
theorem homogeneous_coefficients_mem {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N] {s : ℕ} (y : Fin s → R)
    (hy : RingTheory.Sequence.IsWeaklyRegular N (List.ofFn y)) (n : ℕ)
    (c : (Finset.Nat.antidiagonalTuple s n) → N)
    (hc : (∑ α : Finset.Nat.antidiagonalTuple s n, (∏ i, y i ^ α.val i) • c α) ∈
      (Ideal.ofList (List.ofFn y) ^ (n + 1)) • (⊤ : Submodule R N)) :
    ∀ α : Finset.Nat.antidiagonalTuple s n,
      c α ∈ Ideal.ofList (List.ofFn y) • (⊤ : Submodule R N) := by
  sorry

end RingTheory.Sequence.IsWeaklyRegular
