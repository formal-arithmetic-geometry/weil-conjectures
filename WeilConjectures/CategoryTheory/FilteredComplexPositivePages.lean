/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.FilteredComplexPageHomology

/-!
# Positive pages of a filtered complex

Source: Stacks Project, Homology, Tag 012K and Remark 12.18.2.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The positive-page sequence, without its initial graded complex.
Source: Stacks Project, Homology, Tag 012K, and. -/
theorem filteredComplex_positive_spectralSequence
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    ∃ E : CohomologicalSpectralSequence C 1,
      ∀ (p q r : ℤ) (hr : 1 ≤ r),
        ∃ hBZ : F.complexBoundaries p (p + q) r ≤ F.complexCycles p (p + q) r,
          Nonempty ((E.page r).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ)) := by
  classical
  have hD (r : ℤ) (hr : 1 ≤ r) : Nonempty (FilteredComplexPageDifferential K F r) := by
    obtain ⟨D, _, _⟩ := filteredComplex_page_differential_exists_unique K F r hr
    exact ⟨D⟩
  let D (r : ℤ) (hr : 1 ≤ r) := Classical.choice (hD r hr)
  let E : CohomologicalSpectralSequence C 1 :=
    { page := fun r hr => (D r hr).page
      iso := fun r r' pq hrr' hr =>
        (Classical.choice (filteredComplex_page_homology K F r hr (D r hr) pq)) ≪≫
          eqToIso (congrArg (fun s => filteredComplexPageObject K F s pq) hrr') }
  refine ⟨E, fun p q r hr => ?_⟩
  refine ⟨filteredComplex_boundaries_le_cycles K F p (p + q) r, ?_⟩
  exact ⟨Iso.refl _⟩

end CategoryTheory
