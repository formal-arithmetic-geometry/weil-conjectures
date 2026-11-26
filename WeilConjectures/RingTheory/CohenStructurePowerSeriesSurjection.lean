/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CoefficientResidueSection
import WeilConjectures.RingTheory.CohenRingLiftToCompleteLocal
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Power series presentations of complete local rings

A complete local ring with finitely generated maximal ideal is a quotient of a power series
ring over a characteristic-zero field or a Cohen ring of the residue characteristic.

## Implementation details

The coefficient map comes from `exists_residue_section` in characteristic zero and from
`exists_cohenRing` and `exists_cohenRing_lift` otherwise. The map from power series sends the
variables to generators of the maximal ideal; it is surjective by successive approximation
(`surjective_of_mk_map_comp_surjective`, [Stacks, Tag 0315]), avoiding the finite-module detour
through [Stacks, Tag 031D].

## References

* [Stacks, Tag 032A], part (2) and its proof
* [Stacks, Tag 0315]
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A complete local ring with finitely generated maximal ideal is a quotient of a power series
ring over a characteristic-zero field or a Cohen ring of the residue characteristic. -/
theorem cohen_structure_power_series_surjection
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hfg : (maximalIdeal R).FG) [IsAdicComplete (maximalIdeal R) R]
    (p : ℕ) [CharP (ResidueField R) p] :
    ∃ (n : ℕ) (Λ : Type u) (_ : CommRing Λ),
      (p = 0 → IsField Λ ∧ CharZero Λ) ∧
      (0 < p → IsCohenRing p Λ) ∧
      ∃ φ : MvPowerSeries (Fin n) Λ →+* R, Function.Surjective φ := by
  classical
  obtain ⟨n, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hymem (i : Fin n) : y i ∈ maximalIdeal R := by
    rw [← hy]
    exact Submodule.subset_span ⟨i, rfl⟩
  have presentation (Λ : Type u) [CommRing Λ] (α : Λ →+* R)
      (hα : Function.Surjective ((residue R).comp α)) :
      ∃ φ : MvPowerSeries (Fin n) Λ →+* R, Function.Surjective φ := by
    obtain ⟨φ, hC, hX, _⟩ := MvPowerSeries.exists_ringHom_of_isAdicComplete
      (maximalIdeal R) α n y hymem
    let I : Ideal (MvPowerSeries (Fin n) Λ) := Ideal.span (Set.range MvPowerSeries.X)
    have hmap : I.map φ = maximalIdeal R := by
      rw [Ideal.map_span, ← Set.range_comp]
      simpa only [Function.comp_def, hX] using hy
    have : IsHausdorff (I.map φ) R := hmap.symm ▸ inferInstance
    refine ⟨φ, surjective_of_mk_map_comp_surjective (I := I) φ ?_⟩
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hα (residue R r)
    refine ⟨MvPowerSeries.C a, ?_⟩
    change Ideal.Quotient.mk (I.map φ) (φ (MvPowerSeries.C a)) = _
    rw [hC]
    change Ideal.Quotient.mk (maximalIdeal R) (α a) =
      Ideal.Quotient.mk (maximalIdeal R) r at ha
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha ⊢
    simpa only [hmap] using ha
  rcases CharP.char_is_prime_or_zero (ResidueField R) p with hp | hp
  · obtain ⟨Λ, hcomm, hΛ, ⟨e⟩⟩ := exists_cohenRing p hp (ResidueField R)
    let _ := hcomm
    obtain ⟨α, hα⟩ := exists_cohenRing_lift R p Λ hΛ e
    refine ⟨n, Λ, hcomm, ?_, fun _ ↦ hΛ, presentation Λ α ?_⟩
    · intro hzero
      exact False.elim (hp.ne_zero hzero)
    · rw [hα]
      exact e.surjective.comp Ideal.Quotient.mk_surjective
  · subst p
    have : CharZero (ResidueField R) := CharP.charP_to_charZero (ResidueField R)
    obtain ⟨α, hα⟩ := exists_residue_section R
    refine ⟨n, ResidueField R, inferInstance, fun _ ↦ ⟨Field.toIsField _, inferInstance⟩,
      ?_, presentation (ResidueField R) α ?_⟩
    · intro hpos
      exact False.elim (Nat.lt_irrefl 0 hpos)
    · rw [hα]
      exact Function.surjective_id

end IsLocalRing
