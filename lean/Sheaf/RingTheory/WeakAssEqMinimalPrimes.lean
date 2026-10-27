module

public import Sheaf.RingTheory.WeaklyAssociated
import Sheaf.RingTheory.WeakAssLocalization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Weakly associated primes of a reduced ring

Source: Stacks Project, Algebra, Tag 0EMA, Lemma `lemma-reduced-weakly-ass-minimal`
(blueprint: lem-sfb-reduced-weakass-minimal).
-/

@[expose] public section

universe u

namespace Ideal

/-- The weakly associated primes of a reduced commutative ring are exactly its minimal
primes, without Noetherianity or a finiteness assumption. This includes the zero ring.
Source: Stacks Project, Algebra, Tag 0EMA, Lemma `lemma-reduced-weakly-ass-minimal`
(blueprint: lem-sfb-reduced-weakass-minimal).

Proof:
1. For a prime `p`, put `A = Localization.AtPrime p`. This is nonzero and reduced:
   if `(a/s)^n = 0` for positive `n`, some `t ∉ p` satisfies `t * a^n = 0`.
   Then `(t*a)^n = 0`, so `t*a = 0` and `a/s = 0`.
   This uses `def-weil-pbc-localization-at-prime`.
2. If `p ∈ WeakAss R`, the localization criterion `lem-sc-weakass-localization`
   gives `x ∈ A` whose annihilator has radical `pA`. The module localization of `R`
   identifies with `A` by the same fraction formula and scalar action
   (`def-weil-pbc-module-localization`). The maximal ideal `pA` is proper.
3. Write `x = a/s`. If `a ∉ p`, then `x` is a unit, its annihilator is zero, and
   reducedness gives `pA = 0`. Otherwise `x ∈ pA = radical(Ann(x))`, so some
   positive power of `x` annihilates `x`. Reducedness forces `x = 0`, whose
   annihilator is the whole ring, contradicting properness of `pA`.
4. By `lem-weil-pbc-primes-of-localization`, primes below `p` correspond in order
   to primes of `A`. Since `pA = 0`, any such prime equals `pA`; hence `p` is minimal.
   Conversely, `Ann(1) = 0`, so `1` witnesses weak association of every minimal prime
   by `def-sc-weakly-associated-primes`. The inclusions give equality. In the zero
   ring there are no proper prime ideals, so both sets are empty. -/
theorem weakAss_eq_minimalPrimes (R : Type u) [CommRing R] [IsReduced R] :
    WeakAss R = minimalPrimes R := by
  sorry

end Ideal
