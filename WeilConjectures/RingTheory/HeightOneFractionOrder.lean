/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.WeilDivisorClassGroup
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The normalized order of a fraction at a height-one prime

Source: Stacks Project, Algebra, Tags 00PD and 02MD, and Divisors, Tag 02RJ
(blueprint: def-trf-height-one-fraction-order).

Use the existing length order `Ring.weilOrder` on ring elements. For a fraction,
subtract the order of its denominator from that of its numerator. In a Noetherian
normal domain each height-one localization is a DVR, so the local lengths are
finite on nonzero elements and their difference is the normalized additive valuation.
-/

@[expose] public section

universe u

namespace Ring

/-- The normalized additive valuation of a fraction at a height-one prime.
Source: Stacks Project, Algebra, Tag 00PD (the formula `v(a/b) = v(a) - v(b)`)
and Tag 02MD; Divisors, Tag 02RJ
(blueprint: def-trf-height-one-fraction-order).

The numerator and denominator are the actual fraction presentation returned by
`IsLocalization.sec`; the denominator is a nonzero divisor. The local orders
are the existing length construction `weilOrder`, not an arbitrary valuation.
For nonzero fractions the numerator is also nonzero. In a normal Noetherian
domain the local rings are DVRs, so additivity of length on products makes the
result independent of the presentation and gives a uniformizer value one. -/
noncomputable def weilFractionOrder {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (q : WeilHeightOnePrime R) (x : FractionRing R) : ℤ :=
  weilOrder q (IsLocalization.sec (nonZeroDivisors R) x).1 -
    weilOrder q (IsLocalization.sec (nonZeroDivisors R) x).2.1

end Ring
