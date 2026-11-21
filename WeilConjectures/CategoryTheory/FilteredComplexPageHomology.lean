/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorBoundariesImage

/-!
# Successor homology of a filtered-complex quotient page

Source: Stacks Project, Homology, Tag 012K,
and the displayed cycle, boundary, and differential formulas preceding it.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pullback_kernel {A B T : C} (f : A ⟶ B) (g : B ⟶ T) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply le_kernelSubobject
    have hf := (pullback_factors_iff f (kernelSubobject g) _).mp
      (Subobject.factors_self _)
    simpa only [Category.assoc] using (kernelSubobject_factors_iff g _).mp hf
  · apply Subobject.le_of_factors
    apply (pullback_factors_iff _ _ _).mpr
    apply kernelSubobject_factors
    simpa only [Category.assoc] using kernelSubobject_arrow_comp (f ≫ g)

/-- The homology of the representative differential is the next concrete quotient.
The next page's differential is not needed for this assertion.
Source: Stacks Project, Tag 012K,
and the displayed cycle, boundary, and differential formulas preceding it. -/
theorem filteredComplex_page_homology
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ) :
    Nonempty (D.page.homology pq ≅ filteredComplexPageObject K F (r + 1) pq) := by
  have hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r := by
    unfold DecreasingFiltration.complexCycles
    apply (Subobject.«exists» _).monotone
    apply (Subobject.pullback _).monotone
    apply sup_le_sup_right
    apply inf_le_inf_left
    apply (Subobject.pullback _).monotone
    unfold DecreasingFiltration.complexStep
    have hF := F.antitone_step (show pq.1 + r ≤ pq.1 + (r + 1) by omega)
    have hfac := congrArg (fun φ ↦ φ.f (pq.1 + pq.2 + 1))
      (Subobject.ofLE_arrow hF)
    rw [HomologicalComplex.comp_f] at hfac
    apply imageSubobject_le _
      (((Subobject.ofLE _ _ hF).f (pq.1 + pq.2 + 1)) ≫
        factorThruImageSubobject ((F.step (pq.1 + r)).arrow.f (pq.1 + pq.2 + 1)))
    rw [Category.assoc, imageSubobject_arrow_comp, hfac]
  obtain ⟨f, hfepi, hf⟩ := filteredComplex_successor_cycles_cover K F r hr D pq hZ
  have : Epi f := hfepi
  let b := Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) (r + 1))
  let t := D.page.toCycles ((ComplexShape.up' (r, 1 - r)).prev pq) pq
  have ht : t ≫ D.page.homologyπ pq = 0 := D.page.toCycles_comp_homologyπ _ _
  have hker : kernelSubobject (D.page.homologyπ pq) = imageSubobject t := by
    exact ((ShortComplex.mk t (D.page.homologyπ pq) ht).exact_iff_image_eq_kernel.mp
      (ShortComplex.exact_of_g_is_cokernel _ (D.page.homologyIsCokernel _ _ rfl))).symm
  have himage := filteredComplex_successor_boundaries_image K F r hr D pq hZ f hf
  have heq : imageSubobject b = kernelSubobject (f ≫ D.page.homologyπ pq) := by
    rw [imageSubobject_mono, ← pullback_kernel, hker]
    exact himage.symm
  have w : b ≫ (f ≫ D.page.homologyπ pq) = 0 := by
    apply (kernelSubobject_factors_iff _ _).mp
    rw [← heq]
    simpa only [Category.id_comp] using imageSubobject_factors_comp_self b (𝟙 _)
  have hsc := (ShortComplex.mk b (f ≫ D.page.homologyπ pq) w).exact_iff_image_eq_kernel.mpr
    heq
  exact ⟨hsc.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)⟩

end CategoryTheory
