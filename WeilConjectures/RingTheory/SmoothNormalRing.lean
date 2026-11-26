/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.RingTheory.SmoothNormalDomainApproximation
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import WeilConjectures.RingTheory.NormalOfFlatNormalFibers
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.RingTheory.RegularRingSmoothAscent

/-!
# Smooth algebras over normal rings

A smooth algebra over a normal ring is normal.

## References

* [Stacks, Tag 033C]
-/

@[expose] public section

universe uR uS

namespace RingHom

private theorem smooth_normal_noetherian {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [IsNoetherianRing R]
    {f : R →+* S} (hf : f.Smooth)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.Smooth R S := hf.toAlgebra
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply normal_of_flat_normal_fibers f hf.flat _ hR
  intro p hp
  let : IsRegularRing (p.Fiber S) :=
    Algebra.isRegularRing_of_smooth p.ResidueField (p.Fiber S)
  exact IsRegularRing.isNormalRing (p.Fiber S)

private theorem smooth_normal_domain {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [IsDomain R] [IsIntegrallyClosed R]
    {f : R →+* S} (hf : f.Smooth) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨I, cI, hI, F, hF, ⟨e⟩, hmodels⟩ := hf.exists_noetherian_normal_model_colimit
  have hn := CommRingCat.isNormal_of_filtered_colimit F (fun i ↦ by
    obtain ⟨A, hA, hnoeth, g, hg, hnormal⟩ := hmodels i
    exact smooth_normal_noetherian hg hnormal)
  intro q hq
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime e.toRingHom q
  obtain ⟨hd, hi⟩ := hn p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e' := Localization.localRingEquiv p q e rfl
  exact ⟨e'.symm.injective.isDomain e'.symm, IsIntegrallyClosed.of_equiv e'⟩

/-- A smooth algebra over a normal ring is normal: if every localization of `R` at a prime is
an integrally closed domain, then so is every localization of `S` at a prime. -/
theorem Smooth.isNormalRing {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.Smooth)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.Smooth R S := hf.toAlgebra
  intro q hq
  let p := q.comap f
  let : p.IsPrime := Ideal.comap_isPrime f q
  obtain ⟨hdom, hint⟩ := hR p
  let A := Localization.AtPrime p
  let : IsDomain A := hdom
  let : IsIntegrallyClosed A := hint
  let B := TensorProduct R A S
  have hB := smooth_normal_domain (RingHom.smooth_algebraMap.mpr
    (inferInstance : Algebra.Smooth A B))
  let : Algebra S B := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  have hdisj : Disjoint (M : Set S) (q : Set S) := by
    rw [Set.disjoint_left]
    rintro x ⟨r, hr, rfl⟩ hx
    exact hr hx
  let q' := q.map (algebraMap S B)
  let : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B q hq hdisj
  have hcontract : q'.comap (algebraMap S B) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M B hq hdisj
  obtain ⟨hd, hi⟩ := hB q'
  let : IsDomain (Localization.AtPrime q') := hd
  let : IsIntegrallyClosed (Localization.AtPrime q') := hi
  have : IsLocalization.AtPrime (Localization.AtPrime q') q := by
    simpa only [hcontract] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        M (Localization.AtPrime q') q')
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q')
    (Localization.AtPrime q)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

end RingHom
