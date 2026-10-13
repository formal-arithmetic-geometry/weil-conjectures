/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.CategoryTheory.FilteredQuotientPageMaps
public import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology

/-!
# Maps on successor cycles and the two page projections

Source: Stacks Project, Tag 012K, Lemma 12.24.4 and the cycle formulas.
(blueprint: lem-sp-filtered-quotient-successor-cycle-maps).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtered map has a successor-cycle restriction compatible with the cycle
cover on the current page and the quotient projection on the successor page.
Source: Stacks Project, Tag 012K, Lemma 12.24.4 and the displayed cycle formulas.
(blueprint: lem-sp-filtered-quotient-successor-cycle-maps).

Proof. Choose the step restrictions of t from its preservation property. Cancel
the monic step inclusions to show that they commute with all filtration inclusions.
Cokernel descent gives the graded map g in degree p. The chain map equation and
preservation of F^(p+r+1) show that the map on step p preserves the pullback
of the differential defining successor representatives. Taking the graded image
gives its restriction k to successor cycles. Its composite with the target cycle
inclusion equals the source cycle inclusion followed by g. The same construction
at r gives a cycle restriction kz. By cancellation of the graded cycle inclusion,
k followed by Z_(r+1) to Z_r equals that inclusion followed by kz. The universal
page-map square for m0, together with the equations for fU and fV, implies after
the monic target page cycle inclusion that k followed by fV equals fU followed
by the page cycles map. Cancel that monomorphism to obtain the first equation.
Boundary preservation follows by mapping the image of the differential on step
p-r to its target image. Descend the successor cycle map modulo successor
boundaries; the universal square property for m1 identifies that descended map
with m1. Its projection equation is the second asserted equation. -/
theorem filteredQuotient_successor_cycle_maps
    (U V : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (t : U ⟶ V) (r : ℤ) (hr : 1 ≤ r)
    (DU : FilteredComplexPageDifferential U.obj.obj U.obj.filtration r)
    (DV : FilteredComplexPageDifferential V.obj.obj V.obj.filtration r)
    (DU' : FilteredComplexPageDifferential U.obj.obj U.obj.filtration (r + 1))
    (DV' : FilteredComplexPageDifferential V.obj.obj V.obj.filtration (r + 1))
    (m0 : DU.page ⟶ DV.page) (m1 : DU'.page ⟶ DV'.page)
    (hm0 : FilteredQuotientPageMapProperty U V t r DU DV m0)
    (hm1 : FilteredQuotientPageMapProperty U V t (r + 1) DU' DV' m1)
    (pq : ℤ × ℤ)
    (fU : (U.obj.filtration.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶
      DU.page.cycles pq)
    (fV : (V.obj.filtration.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶
      DV.page.cycles pq)
    (hfU : fU ≫ DU.page.iCycles pq = Subobject.ofLE _ _
      (filteredComplex_cycles_successor_le U.obj.obj U.obj.filtration r pq) ≫
        filteredComplexPageπ U.obj.obj U.obj.filtration r pq)
    (hfV : fV ≫ DV.page.iCycles pq = Subobject.ofLE _ _
      (filteredComplex_cycles_successor_le V.obj.obj V.obj.filtration r pq) ≫
        filteredComplexPageπ V.obj.obj V.obj.filtration r pq) :
    ∃ k : (U.obj.filtration.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶
        (V.obj.filtration.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C),
      k ≫ fV = fU ≫ HomologicalComplex.cyclesMap m0 pq ∧
      filteredComplexPageπ U.obj.obj U.obj.filtration (r + 1) pq ≫ m1.f pq =
        k ≫ filteredComplexPageπ V.obj.obj V.obj.filtration (r + 1) pq := by
  sorry

end CategoryTheory
