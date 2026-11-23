/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCoverExists
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCoverEpi

/-!
# Successor cycles cover the kernel of a page differential

Source: Stacks Project, Homology, Tag 012K, displayed cycle and differential formulas.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The projection of successor graded cycles covers the cycles of the page differential.
Source: Stacks Project, Homology, Tag 012K, the cycle and differential formulas preceding. -/
theorem filteredComplex_successor_cycles_cover
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r) :
    ∃ f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq,
      Epi f ∧ f ≫ D.page.iCycles pq =
        Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq := by
  obtain ⟨f, hf⟩ := filteredComplex_successor_cycles_cover_exists K F r hr D pq hZ
  exact ⟨f, filteredComplex_successor_cycles_cover_epi K F r hr D pq hZ f hf, hf⟩

end CategoryTheory
