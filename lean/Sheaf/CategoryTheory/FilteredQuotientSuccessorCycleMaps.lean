/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.CategoryTheory.FilteredQuotientPageMaps
public import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.CategoryTheory.FilteredQuotientMapRestrictions

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
  classical
  choose s hs using t.hom.preserves
  let iU := Subobject.ofLE (U.obj.filtration.step (pq.1 + 1))
    (U.obj.filtration.step pq.1) (U.obj.filtration.antitone_step (by omega))
  let iV := Subobject.ofLE (V.obj.filtration.step (pq.1 + 1))
    (V.obj.filtration.step pq.1) (V.obj.filtration.antitone_step (by omega))
  have hi : iU ≫ s pq.1 = s (pq.1 + 1) ≫ iV := by
    apply (cancel_mono (V.obj.filtration.step pq.1).arrow).1
    dsimp [iU, iV]
    rw [Category.assoc, hs, ← Category.assoc, Subobject.ofLE_arrow,
      Category.assoc, Subobject.ofLE_arrow, hs]
  let g : U.obj.filtration.gradedPiece pq.1 ⟶ V.obj.filtration.gradedPiece pq.1 :=
    cokernel.map iU iV (s (pq.1 + 1)) (s pq.1) hi
  have hg : U.obj.filtration.complexQuotientπ pq.1 (pq.1 + 1) (by omega) ≫ g =
      s pq.1 ≫ V.obj.filtration.complexQuotientπ pq.1 (pq.1 + 1) (by omega) :=
    cokernel.π_desc _ _ _
  let hBZ := fun (W : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q j : ℤ) (_ : 1 ≤ j) ↦
    filteredComplex_boundaries_le_cycles W.obj.obj W.obj.filtration p (p + q) j
  obtain ⟨kz, k0, hkz, hk0, _⟩ :=
    filteredQuotient_map_restrictions C hBZ U V t pq.1 pq.2 r hr s g hs hg
  obtain ⟨k, k1, hk, hk1, _⟩ :=
    filteredQuotient_map_restrictions C hBZ U V t pq.1 pq.2 (r + 1)
      (by omega) s g hs hg
  have hm0' : m0.f pq = k0 := hm0 pq.1 pq.2 s g kz k0 hs hg hkz hk0
  have hm1' : m1.f pq = k1 := hm1 pq.1 pq.2 s g k k1 hs hg hk hk1
  have hπ0 : filteredComplexPageπ U.obj.obj U.obj.filtration r pq ≫ m0.f pq =
      kz ≫ filteredComplexPageπ V.obj.obj V.obj.filtration r pq := by
    rw [hm0']
    exact hk0
  let jU := Subobject.ofLE _ _
    (filteredComplex_cycles_successor_le U.obj.obj U.obj.filtration r pq)
  let jV := Subobject.ofLE _ _
    (filteredComplex_cycles_successor_le V.obj.obj V.obj.filtration r pq)
  have hj : k ≫ jV = jU ≫ kz := by
    apply (cancel_mono (V.obj.filtration.complexCycles pq.1
      (pq.1 + pq.2) r).arrow).1
    dsimp [jU, jV]
    rw [Category.assoc, Subobject.ofLE_arrow, hk, Category.assoc, hkz,
      ← Category.assoc, Subobject.ofLE_arrow]
  refine ⟨k, ?_, ?_⟩
  · apply (cancel_mono (DV.page.iCycles pq)).1
    calc
      (k ≫ fV) ≫ DV.page.iCycles pq =
          k ≫ jV ≫ filteredComplexPageπ V.obj.obj V.obj.filtration r pq := by
        rw [Category.assoc, hfV]
      _ = jU ≫ kz ≫ filteredComplexPageπ V.obj.obj V.obj.filtration r pq := by
        rw [← Category.assoc, hj, Category.assoc]
      _ = jU ≫ filteredComplexPageπ U.obj.obj U.obj.filtration r pq ≫ m0.f pq := by
        rw [hπ0]
      _ = (fU ≫ HomologicalComplex.cyclesMap m0 pq) ≫ DV.page.iCycles pq := by
        simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
        simpa only [Category.assoc] using
          (congrArg (fun a ↦ a ≫ m0.f pq) hfU).symm
  · rw [hm1']
    exact hk1

end CategoryTheory
