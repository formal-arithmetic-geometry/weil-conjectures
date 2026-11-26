/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.RegularComposition
import WeilConjectures.RingTheory.RegularThroughLocalization
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.GeometricallyRegularFibersOfMaximal
public import Mathlib.RingTheory.Flat.Localization

/-!
# Regular ring maps are local on the target

For a ring map with Noetherian target, regularity can be checked on the induced maps of prime
localizations, or of localizations at maximal ideals.

## Implementation details

Flatness is local (Tag 00HT). At a prime `q` above `p`, the closed fibre of the local map is a
localization of the global fibre at `p`, compatibly with finite purely inseparable residue field
extensions, and a Noetherian ring is regular exactly when its prime localizations are. Each map
at a prime is a further localization of the map at a maximal ideal containing it.

## References

* [Stacks, Tag 07C0]
* [Stacks, Tag 00HT]
-/

@[expose] public section

universe u v

namespace RingHom

/-- For a ring map with Noetherian target, regularity is equivalent to regularity of all
induced maps on prime localizations, and also to regularity at all maximal target ideals. -/
theorem isRegular_iff_localRingHom_prime_and_maximal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (f : R →+* S) :
    (f.IsRegular ↔ ∀ (q : Ideal S) [q.IsPrime],
      (Localization.localRingHom (q.comap f) q f rfl).IsRegular) ∧
    (f.IsRegular ↔ ∀ (m : Ideal S) [m.IsMaximal],
      (Localization.localRingHom (m.comap f) m f rfl).IsRegular) := by
  have hlocal (hf : f.IsRegular) (q : Ideal S) [q.IsPrime] :
      (Localization.localRingHom (q.comap f) q f rfl).IsRegular := by
    let : Algebra R S := f.toAlgebra
    have hf' : (algebraMap R S).IsRegular := hf
    have hcomp : (algebraMap R (Localization.AtPrime q)).IsRegular :=
      hf'.comp_of_fiber_noetherian
        (IsLocalization.isRegular_and_fiber q.primeCompl).1
        (fun p _ ↦ Ideal.isNoetherianRing_fiber p)
    let := (Localization.localRingHom (q.comap f) q f rfl).toAlgebra
    have : IsScalarTower R (Localization.AtPrime (q.comap f))
        (Localization.AtPrime q) :=
      .of_algebraMap_eq fun x ↦
        (Localization.localRingHom_to_map _ _ _ rfl x).symm
    exact isRegular_of_comp_algebraMap_localization (q.comap f).primeCompl hcomp
  have hmax (h : ∀ (m : Ideal S) [m.IsMaximal],
      (Localization.localRingHom (m.comap f) m f rfl).IsRegular) : f.IsRegular := by
    let : Algebra R S := f.toAlgebra
    refine ⟨?_, ?_⟩
    · change Module.Flat R S
      apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
        (fun P ↦ Algebra.linearMap S _)
      intro P _
      let := (Localization.localRingHom (P.comap f) P f rfl).toAlgebra
      have : IsScalarTower R (Localization.AtPrime (P.comap f))
          (Localization.AtPrime P) :=
        .of_algebraMap_eq fun x ↦
          (Localization.localRingHom_to_map _ _ _ rfl x).symm
      have : Module.Flat (Localization.AtPrime (P.comap f)) (Localization.AtPrime P) :=
        (h P).1
      exact Module.Flat.trans R (Localization.AtPrime (P.comap f)) (Localization.AtPrime P)
    · intro p _
      apply Algebra.isGeometricallyRegular_fiber_of_localizations_maximal p
      intro m _
      let := (Localization.localRingHom (m.comap f) m f rfl).toAlgebra
      have : IsScalarTower R (Localization.AtPrime (m.comap f))
          (Localization.AtPrime m) :=
        .of_algebraMap_eq fun x ↦
          (Localization.localRingHom_to_map _ _ _ rfl x).symm
      have hm : (algebraMap (Localization.AtPrime (m.comap f))
          (Localization.AtPrime m)).IsRegular := h m
      have hcomp : (algebraMap R (Localization.AtPrime m)).IsRegular :=
        (IsLocalization.isRegular_and_fiber (m.comap f).primeCompl).1
          |>.comp_of_fiber_noetherian hm (fun p _ ↦ Ideal.isNoetherianRing_fiber p)
      rw [RingHom.IsRegular, toAlgebra_algebraMap] at hcomp
      exact hcomp.2 p
  exact ⟨⟨hlocal, fun h ↦ hmax (fun m _ ↦ h m)⟩, ⟨fun hf m _ ↦ hlocal hf m, hmax⟩⟩

end RingHom
