/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesDifferentialZero

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The successor-cycle inclusion into the page factors through its cycles.
Source: Stacks Project, Homology, Tag 012K, displayed cycle, boundary and
differential formulas preceding. -/
theorem filteredComplex_successor_cycles_cover_exists
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r) :
    ∃ f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq,
      f ≫ D.page.iCycles pq =
        Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq := by
  let a := Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq
  have ha : a ≫ D.page.d pq ((ComplexShape.up' (r, 1 - r)).next pq) = 0 := by
    exact filteredComplex_successor_cycles_differential_zero K F r hr D pq hZ
  let f := D.page.liftCycles a ((ComplexShape.up' (r, 1 - r)).next pq) rfl ha
  refine ⟨f, ?_⟩
  exact D.page.liftCycles_i a _ rfl ha

end CategoryTheory
