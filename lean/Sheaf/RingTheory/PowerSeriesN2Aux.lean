module

public import Sheaf.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! Auxiliary N-2 assertion for power series.

Source: Stacks Project, Algebra, Lemma Tag 032Q.
(blueprint: lem-weil-pbc-power-series-n2-aux).
-/

@[expose] public section

universe u

namespace PowerSeries

/-- The N-2 part of the power-series lemma.  This is the normalization and Tate
argument of Tag 032Q, isolated so that the Noetherian and domain conclusions can
be discharged directly from Mathlib instances.
(blueprint: lem-weil-pbc-power-series-n2-aux). -/
theorem isN2_power_series (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (hR : IsN2 R (FractionRing R)) :
    IsN2 (PowerSeries R) (FractionRing (PowerSeries R)) := by
  sorry

end PowerSeries
