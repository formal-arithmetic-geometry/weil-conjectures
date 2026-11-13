/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal

/-!
# The closed fibre of a strict henselization

The fibre of the structural map of a strict henselization over the distinguished point
contains only the closed point.

## References

* [Stacks Project, Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP)
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
/-- The strict henselization structural fibre over the distinguished point contains no
point other than the closed point. -/
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization s)
    (x : Spec (.of A))
    (h : (e.hom ≫ strictLocalizationToBase s) x =
      s (IsLocalRing.closedPoint Ω)) :
    x = IsLocalRing.closedPoint A := by
  classical
  obtain ⟨R, i, hi, hp, _⟩ := exists_affine_mem_range_and_range_subset
    (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) (by simp)
  let := hi
  have hrange : Set.range s ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint Ω)] using hp
  let xR := IsOpenImmersion.lift i s hrange
  have hfac : xR ≫ i = s := IsOpenImmersion.lift_fac i s hrange
  have hchart := strictHenselization_chart_maximalIdeal R i xR
  rw [hfac] at hchart
  obtain ⟨hlocal, ρ, hρ, hm⟩ := hchart
  let := hlocal
  have hcontract : Spec.map ρ (e.hom x) = xR (IsLocalRing.closedPoint Ω) := by
    apply i.isOpenEmbedding.injective
    have hh : (Spec.map ρ ≫ i) (e.hom x) = (xR ≫ i) (IsLocalRing.closedPoint Ω) := by
      rw [hρ, hfac]
      exact h
    simpa only [Scheme.Hom.comp_apply] using hh
  have hprime : (e.hom x).asIdeal =
      IsLocalRing.maximalIdeal (strictHenselization s) := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (e.hom x).isPrime.ne_top
    · rw [hm, Ideal.map_le_iff_le_comap]
      exact le_of_eq (congrArg PrimeSpectrum.asIdeal hcontract).symm
  have hx : e.hom x = IsLocalRing.closedPoint (strictHenselization s) :=
    PrimeSpectrum.ext hprime
  have hspecial := (IsLocalRing.specializes_closedPoint
    (e.inv (IsLocalRing.closedPoint (strictHenselization s))))
  have hback : IsLocalRing.closedPoint (strictHenselization s) ⤳
      e.hom (IsLocalRing.closedPoint A) := by
    have ht := hspecial.map e.hom.continuous
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id] at ht
    exact ht
  have he : e.hom (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (strictHenselization s) :=
    ((IsLocalRing.specializes_closedPoint _).antisymm hback).eq
  apply e.hom.isOpenEmbedding.injective
  exact hx.trans he.symm
end AlgebraicGeometry.Scheme
