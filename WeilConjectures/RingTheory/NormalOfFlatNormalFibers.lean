/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.FibreRingNoetherian
import WeilConjectures.RingTheory.RegularityRkGoesUp
import WeilConjectures.RingTheory.SerreCriterionNormal
import WeilConjectures.RingTheory.SerreSkGoesUp

/-!
# Normality ascends along flat maps with normal fibres

A flat map of Noetherian rings with normal fibres and normal source has normal target.

## Implementation details

By Serre's criterion, `R` and every fibre satisfy `(R₁)` and `(S₂)`. These conditions ascend
along flat maps (Tags 0339 and 033A), and Serre's criterion applied to `S` gives normality.
Normality means that every prime localization is an integrally closed domain, so zero rings and
zero fibres are allowed.

## References

* [Stacks, Tag 0C22]
* [Stacks, Tag 031S]
* [Stacks, Tag 0339]
* [Stacks, Tag 033A]
-/

@[expose] public section

universe u v

namespace RingHom

/-- A flat map of Noetherian rings with normal fibres and normal source has normal target. -/
theorem normal_of_flat_normal_fibers {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) (hflat : φ.Flat)
    (hfibres : letI : Algebra R S := φ.toAlgebra
      ∀ (p : Ideal R) [p.IsPrime], ∀ (q : Ideal (p.Fiber S)) [q.IsPrime],
        IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let : Algebra R S := φ.toAlgebra
  have hbase := (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS R).mp hR
  have hfibreConditions (p : Ideal R) [p.IsPrime] :
      ∃ (_ : IsNoetherianRing (p.Fiber S)),
        Ring.IsSerreR (p.Fiber S) 1 ∧ Ring.IsSerreS (p.Fiber S) 2 := by
    let := Ideal.isNoetherianRing_fiber (B := S) p
    exact ⟨inferInstance,
      (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS (p.Fiber S)).mp
        (hfibres p)⟩
  apply (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS S).mpr
  constructor
  · apply regularity_rk_goes_up 1 hflat _ hbase.1
    intro p hp
    obtain ⟨hnoeth, hregular, _⟩ := hfibreConditions p
    exact ⟨hnoeth, hregular⟩
  · apply isSerreS_of_flat 2 hflat _ hbase.2
    intro p hp
    obtain ⟨hnoeth, _, hdepth⟩ := hfibreConditions p
    exact ⟨hnoeth, hdepth⟩

end RingHom
