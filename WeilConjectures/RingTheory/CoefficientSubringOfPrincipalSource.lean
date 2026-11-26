/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.FiniteModuleComplete
import Mathlib.RingTheory.Finiteness.Basic

/-! # The image of a complete local principal ideal domain

The image of a complete local principal ideal domain under a local map inducing a surjection onto
the residue field of `R` is a coefficient ring of `R`.

## References

* [Stacks, Tag 032A] (1)
* [Stacks, Tag 0326]
-/

@[expose] public section

universe u v
namespace IsLocalRing

/-- Let `C` be a complete local principal ideal domain with maximal ideal `(p)` and `f : C → R`
a map with `f⁻¹(m_R) = m_C` inducing a surjection onto the residue field of `R`. Then the image
of `f` is a local ring with maximal ideal `m_R ∩ f(C) = (p)`, complete for this ideal, and its
residue field maps isomorphically onto that of `R`. -/
theorem coefficient_subring_of_principal_source
    (R : Type u) [CommRing R] [IsLocalRing R]
    (C : Type v) [CommRing C] [IsDomain C] [IsPrincipalIdealRing C] [IsLocalRing C]
    [IsAdicComplete (maximalIdeal C) C] (p : ℕ)
    (hp : maximalIdeal C = Ideal.span {(p : C)}) (f : C →+* R)
    (hlocal : (maximalIdeal R).comap f = maximalIdeal C)
    (hsurj : Function.Surjective ((residue R).comp f)) :
    ∃ hL : IsLocalRing f.range,
      letI : IsLocalRing f.range := hL
      maximalIdeal f.range = (maximalIdeal R).comap f.range.subtype ∧
      IsAdicComplete ((maximalIdeal R).comap f.range.subtype) f.range ∧
      Function.Bijective
        (Ideal.quotientMap (I := (maximalIdeal R).comap f.range.subtype)
          (maximalIdeal R) f.range.subtype le_rfl) ∧
      (maximalIdeal R).comap f.range.subtype = Ideal.span {(p : f.range)} := by
  have hL : IsLocalRing f.range :=
    IsLocalRing.of_surjective' f.rangeRestrict f.rangeRestrict_surjective
  have hmapped : (maximalIdeal C).map f.rangeRestrict =
      (maximalIdeal R).comap f.range.subtype := by
    rw [← hlocal]
    change (((maximalIdeal R).comap f.range.subtype).comap f.rangeRestrict).map
      f.rangeRestrict = _
    exact Ideal.map_comap_of_surjective f.rangeRestrict f.rangeRestrict_surjective _
  have hmax : maximalIdeal f.range = (maximalIdeal R).comap f.range.subtype := by
    rw [← hmapped]
    exact (map_maximalIdeal_of_surjective f.rangeRestrict
      f.rangeRestrict_surjective).symm
  let : Algebra C f.range := f.rangeRestrict.toAlgebra
  have : Module.Finite C f.range :=
    Module.Finite.of_surjective (Algebra.linearMap C f.range) f.rangeRestrict_surjective
  have hcomplete : IsAdicComplete ((maximalIdeal R).comap f.range.subtype) f.range := by
    rw [← hmapped]
    exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal C) f.range).mpr
      (finite_module_complete_over_complete_noetherian C (maximalIdeal C) f.range)
  refine ⟨hL, hmax, hcomplete, ?_, ?_⟩
  · refine ⟨Ideal.quotientMap_injective, ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨Ideal.Quotient.mk _ (f.rangeRestrict x), ?_⟩
    exact hx
  · rw [← hmapped, hp, Ideal.map_span]
    simp

end IsLocalRing
