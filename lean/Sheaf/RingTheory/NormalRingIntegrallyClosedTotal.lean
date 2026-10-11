/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# A normal ring is integrally closed in its total ring of fractions

Source: Stacks Project, Algebra, Lemma Tag 034M
(blueprint: lem-weil-pbc-normal-ring-integrally-closed-total).

`FractionRing R` is `Localization (nonZeroDivisors R)`, also for rings with zero divisors.
This is the ring specialization of the module localization in
`def-weil-pbc-module-localization`: `Localization S` and `LocalizedModule S R` are
reducibly the same fraction construction. No domain assumption on `R` is made.
-/

universe u

/-- Every integral total fraction of a normal commutative ring comes from the ring.
Source: Stacks Project, Algebra, Lemma Tag 034M
(blueprint: lem-weil-pbc-normal-ring-integrally-closed-total).

Proof (the three steps of the node):
1. Write `x = a/s` with `s` a nonzerodivisor, using
   `def-weil-pbc-module-localization`. The map into the total fraction ring is injective.
   For any prime `p`, `s/1` is nonzero in `R_p`: otherwise some `t` outside `p` has
   `ts = 0`, contradicting regularity of `s`. Map the integral equation for `x`
   (`def-weil-pbc-integral-closure`) into the fraction field of `R_p`
   (`def-weil-pbc-localization-at-prime`).
2. Normality (`def-weil-pbc-normal-ring`) puts this fraction in `R_p`, say `b/f`
   with `f` outside `p`. Clear denominators: some `t` outside `p` satisfies
   `t(fa - bs) = 0`. Thus `(tf)x = tb` in the total fraction ring, and `tf` is
   outside `p`. The ideal `I = {r | rx lies in the image of R}` therefore has an
   element outside each prime ideal.
3. If `I` were proper, `lem-weil-pbc-proper-ideal-contained-in-maximal` would put
   it in a maximal, hence prime, ideal, a contradiction. Thus `1` belongs to `I`,
   so `x` belongs to the image of `R`.
-/
theorem integral_totalFraction_mem_range_of_normal
    (R : Type u) [CommRing R]
    (hnormal : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (x : FractionRing R) (hx : IsIntegral R x) :
    ∃ r : R, algebraMap R (FractionRing R) r = x := by
  sorry
