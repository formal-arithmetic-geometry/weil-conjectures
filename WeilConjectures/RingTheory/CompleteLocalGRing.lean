/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.FiniteSubringGenericFormalFiber
import WeilConjectures.RingTheory.GRingPairsOfPrimes
import WeilConjectures.RingTheory.RegularPowerSeriesGenericFormalFiber

/-!
# Complete local Noetherian rings are G-rings

We prove that a Noetherian complete local ring is a G-ring.

## Implementation details

By the pairs-of-primes criterion, it suffices to check geometric regularity of the generic
formal fibre of a complete local domain `B = S ⧸ q`. Choose a regular complete local subring
`B₀` over which `B` is finite; it is a power-series ring over a field or a Cohen ring. The
statement for `B` reduces by quasi-finite ascent to that for `B₀`, which is handled separately
in characteristic zero (regular fibres are geometrically regular) and in positive
characteristic (where `B₀` is a power-series ring over a field).

## References

* [Stacks, Tag 07PS]
-/

@[expose] public section

universe u

/-- A Noetherian complete local ring is a G-ring. -/
theorem isGRing_of_isNoetherianRing_of_isAdicComplete
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S] : IsGRing S := by
  apply (isGRing_iff_pairsOfPrimes S).mpr
  intro q p hq hp hqp
  let B := S ⧸ q
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hq.ne_top
  let : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have hcomplete := quotient_complete_local S q hq.ne_top
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B := hcomplete.2.2.2
  let P := p.map (Ideal.Quotient.mk q)
  let : P.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
  obtain ⟨B₀, hreg, _, hfinite, _, _, _, hmodel⟩ :=
    IsLocalRing.complete_local_domain_finite_over_regular B
  let : IsRegularLocalRing B₀ := hreg
  let : Module.Finite B₀ B := hfinite
  have hbase := isGeometricallyRegular_genericFormalFiber_of_regular_powerSeries
    B₀ hmodel (P.comap (algebraMap B₀ B))
  have hgeom := isGeometricallyRegular_genericFormalFiber_of_finite_subring
    B B₀ q.ResidueField P hbase
  exact ⟨hgeom.1, hgeom⟩
