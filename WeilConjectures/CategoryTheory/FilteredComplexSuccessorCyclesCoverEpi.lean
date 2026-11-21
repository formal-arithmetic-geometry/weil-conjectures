/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexCycleRepresentativeCorrection
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every successor-cycle map satisfying the representative equation is epic.
Source: Stacks Project, Homology, Tag 012K, displayed cycle, boundary and
differential formulas preceding. -/
theorem filteredComplex_successor_cycles_cover_epi
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r)
    (f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq)
    (hf : f ≫ D.page.iCycles pq =
      Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq) : Epi f := by
  let j := pq + (r, 1 - r)
  have hij : (ComplexShape.up' (r, 1 - r)).Rel pq j := rfl
  obtain ⟨A, t, t', x, y, hepi, ht, hx, hy⟩ :=
    filteredComplex_differential_representatives_cover K F r pq j hij
  let : Epi x := hepi
  let : Epi (filteredComplexPageπ K F r pq) := by
    unfold filteredComplexPageπ
    infer_instance
  let π := x ≫ filteredComplexPageπ K F r pq
  let P := pullback π (D.page.iCycles pq)
  let a : P ⟶ A := pullback.fst π (D.page.iCycles pq)
  let c : P ⟶ D.page.cycles pq := pullback.snd π (D.page.iCycles pq)
  have hc : Epi c := by dsimp [c, π]; infer_instance
  have hfac : a ≫ x ≫ filteredComplexPageπ K F r pq = c ≫ D.page.iCycles pq :=
    pullback.condition
  have hy0 : (a ≫ y) ≫ filteredComplexPageπ K F r j = 0 := by
    have hrep := D.on_representatives A pq j hij t t' x y ht hx hy
    have hk : D.page.iCycles pq ≫ D.d pq j = 0 := D.page.iCycles_d pq j
    calc
      _ = a ≫ x ≫ filteredComplexPageπ K F r pq ≫ D.d pq j := by
        simpa only [Category.assoc] using congrArg (fun g ↦ a ≫ g) hrep.symm
      _ = c ≫ D.page.iCycles pq ≫ D.d pq j := by
        simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ D.d pq j) hfac
      _ = 0 := by rw [hk, comp_zero]
  obtain ⟨B, e, he, z, hz⟩ :=
    filteredComplex_cycle_representative_correction K F r hr pq j hij P
      (a ≫ t) (a ≫ t') (a ≫ x) (a ≫ y)
      (by simpa only [Category.assoc] using congrArg (fun g ↦ a ≫ g) ht)
      (by simpa only [Category.assoc] using congrArg (fun g ↦ a ≫ g) hx)
      (by simpa only [Category.assoc] using congrArg (fun g ↦ a ≫ g) hy) hy0
  let : Epi e := he
  let : Epi c := hc
  have hz' : z ≫ Subobject.ofLE _ _ hZ = e ≫ a ≫ x := by
    apply (cancel_mono (F.complexCycles pq.1 (pq.1 + pq.2) r).arrow).1
    simpa only [Category.assoc, Subobject.ofLE_arrow] using hz
  have hzfac : z ≫ f = e ≫ c := by
    apply (cancel_mono (D.page.iCycles pq)).1
    simp only [Category.assoc, hf]
    rw [← Category.assoc z, hz', Category.assoc, Category.assoc, hfac]
  exact epi_of_epi_fac hzfac

end CategoryTheory
