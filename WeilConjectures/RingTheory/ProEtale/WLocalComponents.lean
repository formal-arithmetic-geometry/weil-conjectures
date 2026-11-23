/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.Topology.SpectralSpace.WLocal.Generalization

/-!
# Connected components of the spectrum of a w-local ring

## Main results

* `IsWLocalRing.connectedComponent_eq_range_comap_localization`: if `R` is w-local, the
  connected component of `Spec R` through a closed point `m` is the image of `Spec R_m`.
* `IsWStrictlyLocalRing.exists_connectedComponent_eq_range_comap_localization`: if `R` is
  w-strictly local, every connected component of `Spec R` is (embedded as) the spectrum of a
  strictly henselian local ring.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

/-- If `R` is w-local, the connected component of `Spec R` containing a closed point `m` is the
image of `Spec R_m`, i.e. the set of primes contained in `m`. -/
theorem IsWLocalRing.connectedComponent_eq_range_comap_localization [IsWLocalRing R]
    (m : Ideal R) [m.IsMaximal] :
    connectedComponent (⟨m, inferInstance⟩ : PrimeSpectrum R) =
      Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))) := by
  rw [WLocalSpace.connectedComponent_eq_setOf_specializes (mem_closedPoints_iff.mpr
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr ‹_›)),
    PrimeSpectrum.localization_comap_range (Localization.AtPrime m) m.primeCompl]
  ext p
  simp only [Set.mem_ofPred_eq, ← PrimeSpectrum.le_iff_specializes]
  exact (Set.disjoint_compl_left_iff_subset (s := (m : Set R))).symm

/-- If `R` is w-strictly local, every connected component of `Spec R` is the spectrum of a
strictly henselian local ring: it is the image of the embedding `Spec R_m → Spec R` for some
maximal ideal `m` with `R_m` strictly henselian. -/
theorem IsWStrictlyLocalRing.exists_connectedComponent_eq_range_comap_localization
    [IsWStrictlyLocalRing R] (x : PrimeSpectrum R) :
    ∃ (m : Ideal R) (_ : m.IsMaximal),
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) ∧
      Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))) ∧
      connectedComponent x =
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))) := by
  obtain ⟨c, hc, hxc⟩ := exists_isClosed_specializes x
  have hm : c.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal c).mp hc
  refine ⟨c.asIdeal, hm, IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization _,
    PrimeSpectrum.localization_comap_isEmbedding _ c.asIdeal.primeCompl, ?_⟩
  rw [← IsWLocalRing.connectedComponent_eq_range_comap_localization c.asIdeal]
  exact (connectedComponent_eq (ConnectedComponents.coe_eq_coe'.mp
    hxc.connectedComponents_mk_eq)).symm
