/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import WeilConjectures.RingTheory.PowerSeriesN2Aux
import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# Power series over a Japanese domain

Over a Noetherian N-2 domain, the one-variable formal power series ring is a Noetherian N-2
domain.

## References

* Stacks Project, Algebra, Lemma Tag 032Q
-/


@[expose] public section

universe u

namespace PowerSeries

/-- Over a Noetherian N-2 domain, the one-variable formal power series ring is a
Noetherian N-2 domain. -/

theorem noetherian_domain_isN2 (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (hR : IsN2 R (FractionRing R)) :
    IsNoetherianRing (PowerSeries R) ∧
      IsDomain (PowerSeries R) ∧
      IsN2 (PowerSeries R) (FractionRing (PowerSeries R)) := by
  exact ⟨inferInstance, inferInstance, isN2_power_series R hR⟩

end PowerSeries
