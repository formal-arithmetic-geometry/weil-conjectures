/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.CategoryTheory.FilteredQuotientPageMaps
public import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.CategoryTheory.FilteredQuotientSuccessorCycleMaps
import Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCover

/-!
# Naturality of normalized successor comparisons

Source: Stacks Project, Tag 012K, Lemma 12.24.4.
(blueprint: lem-sp-filtered-quotient-homology-naturality).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The normalized homology comparison commutes with canonical page maps.
No spectral sequence or functor is constructed in this assertion.
Source: Stacks Project, Tag 012K, Lemma 12.24.4, using the explicit cycle formulas.
(blueprint: lem-sp-filtered-quotient-homology-naturality).

Proof. Choose the unique step restrictions of the filtered map and their graded
quotient maps. Restrict the latter to both r-cycles and successor cycles using
the pullback and image formulas. These restrictions commute with the inclusion
of successor cycles into r-cycles, by cancellation of the graded cycle inclusion.
Let f_U and f_V be the epic successor-cycle covers of the page cycle objects.
After the monic page cycle inclusion, the equation asserting that f_U followed
by the cycles map equals the successor restriction followed by f_V reduces to
the page-map representative square and the preceding inclusion square. Cancel
that monomorphism to obtain the equation on cycle objects. Precompose the desired
homology naturality equation with f_U followed by the homology projection; this
is epic. Homology projection naturality and the equation on cycle objects rewrite
the left side to the successor restriction followed by the successor quotient
projection, by normalization of e_V. Normalization of e_U and the successor
page-map square rewrite the right side to the same composite. Cancel the epic
cover to conclude. This uses neither finiteness nor any choice of arbitrary
homology isomorphisms. -/
theorem filteredQuotient_homology_naturality
    (D : ∀ (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (r : ℤ) (_hr : 1 ≤ r),
      FilteredComplexPageDifferential U.obj.obj U.obj.filtration r)
    (m : ∀ {U V : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)}
      (_t : U ⟶ V) (r : ℤ) (hr : 1 ≤ r),
      (D U r hr).page ⟶ (D V r hr).page)
    (hm : ∀ U V (t : U ⟶ V) r hr,
      FilteredQuotientPageMapProperty (C := C) U V t r (D U r hr) (D V r hr) (m t r hr))
    (e : ∀ (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
      (D U r hr).page.homology pq ≅
        filteredComplexPageObject U.obj.obj U.obj.filtration (r + 1) pq)
    (he : ∀ (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
      FilteredComplexHomologyNormalized (C := C) U.obj.obj U.obj.filtration r (D U r hr) pq
        (e U r hr pq))
    (U V : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (t : U ⟶ V) (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    HomologicalComplex.homologyMap (m t r hr) pq ≫ (e V r hr pq).hom =
      (e U r hr pq).hom ≫ (m t (r + 1) (le_trans hr (Int.le_add_one le_rfl))).f pq := by
  have hZU := filteredComplex_cycles_successor_le U.obj.obj U.obj.filtration r pq
  have hZV := filteredComplex_cycles_successor_le V.obj.obj V.obj.filtration r pq
  obtain ⟨fU, hfUepi, hfU⟩ := filteredComplex_successor_cycles_cover
    U.obj.obj U.obj.filtration r hr (D U r hr) pq hZU
  obtain ⟨fV, _, hfV⟩ := filteredComplex_successor_cycles_cover
    V.obj.obj V.obj.filtration r hr (D V r hr) pq hZV
  have : Epi fU := hfUepi
  obtain ⟨k, hk0, hk1⟩ := filteredQuotient_successor_cycle_maps U V t r hr
    (D U r hr) (D V r hr)
    (D U (r + 1) (le_trans hr (Int.le_add_one le_rfl)))
    (D V (r + 1) (le_trans hr (Int.le_add_one le_rfl)))
    (m t r hr) (m t (r + 1) (le_trans hr (Int.le_add_one le_rfl)))
    (hm U V t r hr) (hm U V t (r + 1) (le_trans hr (Int.le_add_one le_rfl))) pq fU fV hfU hfV
  apply (cancel_epi (fU ≫ (D U r hr).page.homologyπ pq)).1
  calc
    (fU ≫ (D U r hr).page.homologyπ pq) ≫
        (HomologicalComplex.homologyMap (m t r hr) pq ≫ (e V r hr pq).hom) =
      fU ≫ HomologicalComplex.cyclesMap (m t r hr) pq ≫
        (D V r hr).page.homologyπ pq ≫ (e V r hr pq).hom := by
          rw [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
    _ = k ≫ filteredComplexPageπ V.obj.obj V.obj.filtration (r + 1) pq := by
      rw [← Category.assoc fU, ← hk0]
      simp only [Category.assoc, he V r hr pq hZV fV hfV]
    _ = filteredComplexPageπ U.obj.obj U.obj.filtration (r + 1) pq ≫
        (m t (r + 1) (le_trans hr (Int.le_add_one le_rfl))).f pq := hk1.symm
    _ = (fU ≫ (D U r hr).page.homologyπ pq) ≫
        ((e U r hr pq).hom ≫ (m t (r + 1) (le_trans hr (Int.le_add_one le_rfl))).f pq) := by
      simpa only [Category.assoc] using
        (congrArg (fun a ↦ a ≫ (m t (r + 1) (le_trans hr (Int.le_add_one le_rfl))).f pq)
          (he U r hr pq hZU fU hfU)).symm

end CategoryTheory
