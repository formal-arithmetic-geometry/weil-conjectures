/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Power series over a Noetherian normal domain

Source: Stacks Project, Algebra, Lemma 10.37.9 (Tag 0BI0)
(blueprint: lem-weil-pbc-power-series-normal-domain).

The one-variable ring is Mathlib's `PowerSeries R`, the one-variable case of the
recorded power series notion.
Normality for a domain is `IsIntegrallyClosed`, integrality in its fraction field.
-/

@[expose] public section

universe u

namespace PowerSeries

/-- A one-variable power series ring over a Noetherian normal domain is a Noetherian normal
 domain. Source: Stacks Project, Algebra, Lemma 10.37.9 (Tag 0BI0)
(blueprint: lem-weil-pbc-power-series-normal-domain).

Proof following the node's five steps:

1. Apply `lem-weil-pbc-power-series-noetherian` and `lem-weil-pbc-power-series-domain` with
one variable. This gives Noetherianity and the domain property; its fraction field exists.
2. Put `K = Frac(R)`. Map coefficients into `K` and embed the power series into the Laurent
series field `K((x))` (`def-weil-pbc-laurent-series`, `lem-weil-pbc-laurent-series-field`). Both
maps are injective. By `lem-weil-pbc-fraction-field-lift`, their composite extends injectively
from `Frac(R[[x]])` into `K((x))`. Its power series image has no negative coefficients and all
coefficients belong to `R`.
3. If a nonzero integral element `v` has lowest term `c_n x^n`, almost integrality
(`lem-weil-pbc-almost-integral-integral`, `def-weil-pbc-almost-integral`) supplies a nonzero
power series `h` with `h v^e` in the power series ring for every natural `e`. If `h` has lowest
term `b_m x^m`, the lowest term of `h v^e` has degree `m + n*e` and coefficient `b_m c_n^e`.
Thus these degrees are nonnegative and these coefficients belong to `R`. Taking `e = m + 1`
rules out `n < 0`. The coefficient condition makes `c_n` almost integral over `R`; since `R`
is Noetherian, it is integral over `R`, and normality of `R` puts it in `R`.
4. For an integral element `w`, first deduce that every negative coefficient vanishes (the
zero element is immediate). Inductively suppose coefficients below `N` belong to `R`.
Subtract their finite polynomial from `w`. The difference remains integral because integral
elements form a subring (`def-weil-pbc-integral-closure`). If its coefficient at `N` is zero,
it belongs to `R`; otherwise step 3 applies to that lowest coefficient and puts it in `R`.
5. All coefficients now lie in `R` and all negative coefficients vanish, so they define a
power series `f` over `R`. Its Laurent image equals that of `w`; injectivity of the extended
fraction-field map gives `w = f`. This proves integral closedness, together with step 1's
Noetherianity and domain property. -/
theorem noetherian_normal_domain (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R] :
    IsNoetherianRing (PowerSeries R) ∧
      IsDomain (PowerSeries R) ∧ IsIntegrallyClosed (PowerSeries R) := by
  sorry

end PowerSeries
