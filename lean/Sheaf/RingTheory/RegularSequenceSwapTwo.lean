/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Swapping a regular sequence of length two

Source: Stacks Project, Algebra, proof of Lemma Tag 07DW, case `r = 2`
(blueprint: lem-weil-pbc-regular-sequence-swap-two).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- If `[a, b]` is regular on the ring and `b` is a nonzerodivisor on the ring, then
`[b, a]` is regular on the ring. Source: Stacks Project, Algebra, proof of Lemma Tag 07DW,
case `r = 2` (blueprint: lem-weil-pbc-regular-sequence-swap-two).

Proof from the node, using `def-weil-pbc-regular-sequence`:
1. Unwind regularity: `a` is a nonzerodivisor on `R`, `b` is a nonzerodivisor on
   `R/(a)`, and `R/(a,b)` is nonzero. The first condition for the swapped sequence is
   the additional hypothesis on `b`. Its final quotient is nonzero because the
   ideals `(a,b)` and `(b,a)` coincide.
2. To check that `a` is a nonzerodivisor on `R/(b)`, suppose `ax = by`. The class of
   `y` is killed by `b` in `R/(a)`, so `y = az` for some `z`. Thus `a(x - bz) = 0`.
   Injectivity of multiplication by `a` gives `x = bz`, so the class of `x` in
   `R/(b)` vanishes. These three conditions give regularity of `[b, a]`. -/
theorem IsRegular.swap_of_isSMulRegular {R : Type u} [CommRing R] {a b : R}
    (hab : IsRegular R [a, b]) (hb : IsSMulRegular R b) : IsRegular R [b, a] := by
  sorry

end RingTheory.Sequence
