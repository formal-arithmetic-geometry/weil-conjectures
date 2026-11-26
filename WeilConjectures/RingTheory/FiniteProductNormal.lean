/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Finite products of normal rings

A finite product of normal rings is normal.

## Implementation details

Normality is the condition that every localization at a prime is an integrally closed domain,
expressed with `IsDomain`, `IsIntegrallyClosed`, and `Localization.AtPrime`. A prime of a finite
product comes from a prime of one factor, and projection onto that factor identifies the prime
localizations.

## References

* [Stacks, Tag 0CYA]
* [Stacks, Tag 0309]
* [Stacks, Tag 00GV]
-/

@[expose] public section

universe u v

namespace Pi

/-- A finite product of commutative normal rings is normal: every localization at a prime is
an integrally closed domain. -/
theorem isNormalRing_of_finite {I : Type u} [Finite I] (R : I → Type v)
    [∀ i : I, CommRing (R i)]
    (hR : ∀ (i : I) (p : Ideal (R i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (∀ i : I, R i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  intro p hp
  obtain ⟨i, q, hq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (⟨p, hp⟩ : PrimeSpectrum (∀ i, R i))
  have hpq : q.asIdeal.comap (Pi.evalRingHom R i) = p :=
    congrArg PrimeSpectrum.asIdeal hq
  subst p
  obtain ⟨hd, hc⟩ := hR i q.asIdeal
  let e := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
    (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
  exact ⟨e.toMulEquiv.isDomain_iff.mpr hd, IsIntegrallyClosed.of_equiv e.symm⟩

end Pi
