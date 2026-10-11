/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.Perfect

/-!
# Vanishing differentials over a perfect field

Source: Stacks Project, Algebra, Lemma 10.158.2 (Tag 031W)
(blueprint: lem-weil-pbc-differential-zero-iff-pth-power).
-/

@[expose] public section

universe u v

namespace KaehlerDifferential

/-- Over a perfect field `k` of prime characteristic `p`, the universal differential of
`a : K` vanishes exactly when `a` is a `p`-th power in the extension field `K`.
Source: Stacks Project, Algebra, Tag 031W
(blueprint: lem-weil-pbc-differential-zero-iff-pth-power).

Proof (the node's p-basis route, following More on Algebra, Tags 07P1 and 07P2):
1. The Leibniz rule gives `d (b ^ p) = p • b ^ (p - 1) • d b = 0` in characteristic `p`
   (def-weil-pbc-kahler-differentials), proving the reverse implication.
2. Frobenius is a ring homomorphism in characteristic `p`; its image `K^p` is a subfield,
   since inverses of powers are powers. Perfection of `k` implies `k ⊆ K^p`, so `k K^p = K^p`.
3. Choose a p-basis `(t_i)` of `K` over `K^p` by lem-weil-pbc-p-basis-exists. Its monomials
   with finite support and exponents less than `p` are a basis over `K^p`. Since `k K^p = K^p`,
   lem-weil-pbc-p-basis-differentials-basis makes `(d t_i)` a basis of the differentials.
4. Expand `a` in these monomials with coefficients `c_E` in `K^p`. Their differentials vanish
   by step 1. The Leibniz rule (def-weil-pbc-kahler-differentials) makes the coefficient of
   `d t_i` in `d a` equal to the sum of `e_i c_E t^(E - epsilon_i)` for `e_i ≥ 1`.
   If `d a = 0`, independence of the `d t_i` makes each such sum zero. For fixed `i`, the
   reduced monomials are distinct basis elements over `K^p`; their coefficients `e_i c_E`
   belong to `K^p`. Independence forces these coefficients to vanish. Since `1 ≤ e_i < p`,
   `e_i` is invertible, so `c_E = 0` whenever `e_i ≥ 1`. Every nonconstant monomial has such
   an index, leaving only the constant coefficient. Thus `a ∈ K^p`, as required. -/
theorem D_eq_zero_iff_exists_pow_of_perfectField
    (p : ℕ) [Fact p.Prime] (k : Type u) (K : Type v)
    [Field k] [Field K] [Algebra k K] [CharP k p] [PerfectField k] (a : K) :
    D k K a = 0 ↔ ∃ b : K, a = b ^ p := by sorry

end KaehlerDifferential
