/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import WeilConjectures.AlgebraicGeometry.NormalLocusAssociatedPrime

/-! # Openness of the normal locus

## References

* [Stacks, Tag 0332]
-/

@[expose] public section

universe u
namespace AlgebraicGeometry

/-- The normal locus of a Noetherian domain with a normal principal localization is open
(Stacks, Tag 0332). -/
theorem normal_locus_isOpen
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (f : R) (hf : f ≠ 0)
    (hf_normal : IsDomain (Localization.Away f) ∧
      IsIntegrallyClosed (Localization.Away f)) :
    IsOpen {p : PrimeSpectrum R |
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal)} := by
  classical
  let E : Set (PrimeSpectrum R) :=
    {q | q.asIdeal ∈ associatedPrimes R (R ⧸ Ideal.span {f}) ∧
      ¬ (IsDomain (Localization.AtPrime q.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime q.asIdeal))}
  have hE : E.Finite := by
    have hfin := (associatedPrimes.finite R (R ⧸ Ideal.span {f})).preimage
      (fun _ _ _ _ h ↦ PrimeSpectrum.ext h)
    exact hfin.subset (fun _ h ↦ h.1)
  have hcompl :
      {p : PrimeSpectrum R |
        ¬ (IsDomain (Localization.AtPrime p.asIdeal) ∧
          IsIntegrallyClosed (Localization.AtPrime p.asIdeal))} =
        ⋃ q ∈ E, PrimeSpectrum.zeroLocus (q.asIdeal : Set R) := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hqa, hqp, hqn⟩ :=
        exists_nonNormal_associatedPrime_le f hf hf_normal p hp
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr
        ⟨⟨hqa, hqn⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hqp⟩⟩
    · intro hp hpn
      obtain ⟨q, hqp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hqE, hqp⟩ := Set.mem_iUnion.mp hqp
      have hle : q.asIdeal ≤ p.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hqp
      let A := Localization.AtPrime p.asIdeal
      let B := Localization.AtPrime q.asIdeal
      have hsub : p.asIdeal.primeCompl ≤ q.asIdeal.primeCompl :=
        fun x hx hqx ↦ hx (hle hqx)
      let : Algebra A B := IsLocalization.localizationAlgebraOfSubmonoidLe A B
        p.asIdeal.primeCompl q.asIdeal.primeCompl hsub
      have : IsScalarTower R A B :=
        IsLocalization.localization_isScalarTower_of_submonoid_le A B
          p.asIdeal.primeCompl q.asIdeal.primeCompl hsub
      have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap R A)) B :=
        IsLocalization.isLocalization_of_submonoid_le A B
          p.asIdeal.primeCompl q.asIdeal.primeCompl hsub
      have : IsIntegrallyClosed A := hpn.2
      have hM : q.asIdeal.primeCompl.map (algebraMap R A) ≤ nonZeroDivisors A := by
        rintro x ⟨r, hr, rfl⟩
        rw [mem_nonZeroDivisors_iff_ne_zero]
        intro hz
        have hrzero : r = 0 :=
          (IsLocalization.injective A p.asIdeal.primeCompl_le_nonZeroDivisors) (by simpa using hz)
        exact hr (hrzero ▸ q.asIdeal.zero_mem)
      exact hqE.2 ⟨inferInstance, isIntegrallyClosed_of_isLocalization B _ hM⟩
  rw [← isClosed_compl_iff]
  change IsClosed {p : PrimeSpectrum R |
    ¬ (IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal))}
  rw [hcompl]
  exact hE.isClosed_biUnion (fun q _ ↦ PrimeSpectrum.isClosed_zeroLocus _)

end AlgebraicGeometry
