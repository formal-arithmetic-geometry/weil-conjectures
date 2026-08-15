/-
Auxiliary divisor lemma for Chapter 3 of `weil_conjectures_chapter3.tex`,
placed here because `#find_home` locates it in `Mathlib.NumberTheory.Divisors`.
-/
module

public import Mathlib.NumberTheory.Divisors

/-!
# Positivity of quotients by divisors

This file records `Weil.natDiv_pos_of_mem_divisors`: for `r ∈ m.divisors`,
the quotient `m / r` is positive.  It is a candidate for
`Mathlib.NumberTheory.Divisors`.
-/

@[expose] public section

namespace Weil

/-- `lemma:weil-positive-divisor-quotient-positive`.  A quotient by a
positive divisor is positive; the hypothesis `0 < m` is retained from the
text although the divisor-membership lemmas do not need it. -/
theorem natDiv_pos_of_mem_divisors {m r : ℕ} (_hm : 0 < m)
    (hr : r ∈ m.divisors) : 0 < m / r :=
  Nat.div_pos (Nat.divisor_le hr) (Nat.pos_of_mem_divisors hr)

end Weil
