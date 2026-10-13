/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.CategoryTheory.FilteredComplexQuotientCoherence
import Sheaf.CategoryTheory.FilteredComplexQuotientComponents
import Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology

/-! # Descent of filtered maps to coherent quotient pages

Source: Stacks Project, Homology, Tag 012K, lemma-functorial.
(blueprint: lem-weil-pbc-filtered-quotient-map).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtered map descends to quotient pages with representative-fixed comparisons.
This statement has no sheaves, augmented resolutions or first-page identifications.
Source: Stacks Project, Tag 012K, lemma-functorial.
(blueprint: lem-weil-pbc-filtered-quotient-map).

Proof. Choose the uniquely determined restrictions of b to the filtration steps.
The chain-map equation takes a representative whose differential belongs to the
(p+r)-th step to another such representative. The induced map on the graded quotient
therefore takes Z_r into Z'_r. The same equation takes the image of differentials
from the (p-r+1)-th step into the corresponding target image, and hence takes B_r
into B'_r. Apply the cokernel universal property to these inclusions and conjugate
by e and e' to obtain the page components. The representative differential equations
in the two coherence hypotheses show that these components commute with d_r:
precompose with the epimorphism from unquotiented cycle representatives and use
b.comm. At unrelated bidegrees both differentials vanish. For successor compatibility,
precompose with the epimorphism from Z_(r+1) onto the cycles of the r-page, followed
by the homology projection. The successor equations in the two coherence hypotheses
identify both composites with the induced map on Z_(r+1)/B_(r+1). Cancel this
composite epimorphism. These chain maps and successor squares define N; the cokernel
factorization equation gives its asserted action on every test object. Pullbacks of
epimorphisms suffice for local lifting, so no projectivity or finiteness is assumed. -/
theorem filteredComplex_quotient_map
    (K K' : CochainComplex C ℤ) (F : DecreasingFiltration K) (F' : DecreasingFiltration K')
    (E E' : CohomologicalSpectralSequence C 1)
    (e : ∀ (p q r : ℤ) (hr : 1 ≤ r),
      (E.page r hr).X (p, q) ≅ filteredComplexPageObject K F r (p, q))
    (e' : ∀ (p q r : ℤ) (hr : 1 ≤ r),
      (E'.page r hr).X (p, q) ≅ filteredComplexPageObject K' F' r (p, q))
    (hc : FilteredComplexQuotientCoherence K F E e)
    (hc' : FilteredComplexQuotientCoherence K' F' E' e')
    (b : K ⟶ K')
    (hb : ∀ p : ℤ, ∃ s : (F.step p : CochainComplex C ℤ) ⟶
        (F'.step p : CochainComplex C ℤ),
      s ≫ (F'.step p).arrow = (F.step p).arrow ≫ b) :
    ∃ N : E ⟶ E', ∀ (A : C) (p q r : ℤ) (hr : 1 ≤ r)
      (x : A ⟶ (F.step p : CochainComplex C ℤ).X (p + q))
      (y : A ⟶ (F'.step p : CochainComplex C ℤ).X (p + q))
      (z : A ⟶ (F.complexCycles p (p + q) r : C))
      (z' : A ⟶ (F'.complexCycles p (p + q) r : C)),
      x ≫ (F.step p).arrow.f (p + q) ≫ b.f (p + q) =
        y ≫ (F'.step p).arrow.f (p + q) →
      z ≫ (F.complexCycles p (p + q) r).arrow =
        x ≫ (F.complexQuotientπ p (p + 1) (by omega)).f (p + q) →
      z' ≫ (F'.complexCycles p (p + q) r).arrow =
        y ≫ (F'.complexQuotientπ p (p + 1) (by omega)).f (p + q) →
      z ≫ filteredComplexPageπ K F r (p, q) ≫ (e p q r hr).inv ≫
          (N.hom r hr).f (p, q) =
        z' ≫ filteredComplexPageπ K' F' r (p, q) ≫ (e' p q r hr).inv := by
  classical
  choose s hs using hb
  obtain ⟨t, g, m, ht, hg, hm⟩ := filteredComplex_quotient_components K K' F F' b s hs
  choose D a ha using hc.differential
  choose D' a' ha' using hc'.differential
  have hsi (p n : ℤ) : (s p).f n ≫ (F'.step p).arrow.f n =
      (F.step p).arrow.f n ≫ b.f n := by
    exact congrArg (fun f : (F.step p : CochainComplex C ℤ) ⟶ K' ↦ f.f n) (hs p)
  have hrep (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) (A : C)
      (x : A ⟶ (F.step pq.1 : CochainComplex C ℤ).X (pq.1 + pq.2))
      (z : A ⟶ (F.complexCycles pq.1 (pq.1 + pq.2) r : C))
      (hz : z ≫ (F.complexCycles pq.1 (pq.1 + pq.2) r).arrow =
        x ≫ (F.complexQuotientπ pq.1 (pq.1 + 1) (by omega)).f (pq.1 + pq.2)) :
      (z ≫ g r hr pq) ≫ (F'.complexCycles pq.1 (pq.1 + pq.2) r).arrow =
        (x ≫ (s pq.1).f (pq.1 + pq.2)) ≫
          (F'.complexQuotientπ pq.1 (pq.1 + 1) (by omega)).f (pq.1 + pq.2) := by
    calc
      _ = z ≫ (F.complexCycles pq.1 (pq.1 + pq.2) r).arrow ≫
          t pq.1 (pq.1 + pq.2) := by rw [Category.assoc, hg]
      _ = (x ≫ (F.complexQuotientπ pq.1 (pq.1 + 1) (by omega)).f
          (pq.1 + pq.2)) ≫ t pq.1 (pq.1 + pq.2) := by rw [← Category.assoc, hz]
      _ = _ := by rw [Category.assoc, ← ht, ← Category.assoc]
  have hcomm (r : ℤ) (hr : 1 ≤ r) (i j : ℤ × ℤ) :
      m r hr i ≫ (D' r hr).d i j = (D r hr).d i j ≫ m r hr j := by
    by_cases hij : (ComplexShape.up' (r, 1 - r)).Rel i j
    · obtain ⟨A, x, y, z, w, hepi, hxy, hz, hw⟩ :=
        filteredComplex_differential_representatives_cover K F r i j hij
      have : Epi z := hepi
      have : Epi (filteredComplexPageπ K F r i) := by
        unfold filteredComplexPageπ
        infer_instance
      apply (cancel_epi (z ≫ filteredComplexPageπ K F r i)).1
      have hxy' : (x ≫ (s i.1).f (i.1 + i.2)) ≫
          (F'.step i.1).arrow.f (i.1 + i.2) ≫ K'.d (i.1 + i.2) (j.1 + j.2) =
          (y ≫ (s j.1).f (j.1 + j.2)) ≫ (F'.step j.1).arrow.f (j.1 + j.2) := by
        simp only [Category.assoc, hsi, reassoc_of% hsi, b.comm]
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ b.f (j.1 + j.2)) hxy
      have hleft := (D' r hr).on_representatives A i j hij
        (x ≫ (s i.1).f (i.1 + i.2)) (y ≫ (s j.1).f (j.1 + j.2))
        (z ≫ g r hr i) (w ≫ g r hr j) hxy'
        (hrep r hr i A x z hz) (hrep r hr j A y w hw)
      have hright := (D r hr).on_representatives A i j hij x y z w hxy hz hw
      calc
        (z ≫ filteredComplexPageπ K F r i) ≫
            (m r hr i ≫ (D' r hr).d i j) =
            (w ≫ g r hr j) ≫ filteredComplexPageπ K' F' r j := by
          simpa only [Category.assoc, reassoc_of% hm] using hleft
        _ = (w ≫ filteredComplexPageπ K F r j) ≫ m r hr j := by
          simp only [Category.assoc, hm]
        _ = (z ≫ filteredComplexPageπ K F r i) ≫
            ((D r hr).d i j ≫ m r hr j) := by
          simpa only [Category.assoc] using
            congrArg (fun f ↦ f ≫ m r hr j) hright.symm
    · simp only [(D r hr).shape i j hij, (D' r hr).shape i j hij,
        comp_zero, zero_comp]
  let P (r : ℤ) (hr : 1 ≤ r) : (D r hr).page ⟶ (D' r hr).page :=
    { f := m r hr
      comm' := fun i j _ ↦ hcomm r hr i j }
  let n (r : ℤ) (hr : 1 ≤ r) : E.page r hr ⟶ E'.page r hr :=
    (a r hr).hom ≫ P r hr ≫ (a' r hr).inv
  have hai' (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
      (a' r hr).inv.f (p, q) = (e' p q r hr).inv := by
    apply (cancel_mono (e' p q r hr).hom).1
    conv_lhs => rw [← ha' r hr p q, ← HomologicalComplex.comp_f]
    simp only [Iso.inv_hom_id, HomologicalComplex.id_f]
  have hai (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
      (a r hr).inv.f (p, q) = (e p q r hr).inv := by
    apply (cancel_mono (e p q r hr).hom).1
    conv_lhs => rw [← ha r hr p q, ← HomologicalComplex.comp_f]
    simp only [Iso.inv_hom_id, HomologicalComplex.id_f]
  have hn (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
      (n r hr).f (p, q) = (e p q r hr).hom ≫ m r hr (p, q) ≫
        (e' p q r hr).inv := by
    simp only [n, HomologicalComplex.comp_f, ha, hai', P]
  have hsucc (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
      HomologicalComplex.homologyMap (n r hr) pq ≫
          (E'.iso r (r + 1) pq rfl hr).hom =
        (E.iso r (r + 1) pq rfl hr).hom ≫ (n (r + 1) (by omega)).f pq := by
    have hZ := filteredComplex_cycles_successor_le K F r pq
    have hZ' := filteredComplex_cycles_successor_le K' F' r pq
    let inc := Subobject.ofLE _ _ hZ
    let inc' := Subobject.ofLE _ _ hZ'
    have hinc : inc ≫ g r hr pq = g (r + 1) (by omega) pq ≫ inc' := by
      apply (cancel_mono (F'.complexCycles pq.1 (pq.1 + pq.2) r).arrow).1
      simp only [Category.assoc, hg, inc, inc', Subobject.ofLE_arrow,
        reassoc_of% Subobject.ofLE_arrow]
    obtain ⟨f, hfepi, hf⟩ := filteredComplex_successor_cycles_cover K F r hr (D r hr) pq hZ
    have : Epi f := hfepi
    let fE := f ≫ HomologicalComplex.cyclesMap (a r hr).inv pq
    have : IsIso (HomologicalComplex.cyclesMap (a r hr).inv pq) := by
      change IsIso (HomologicalComplex.cyclesMapIso (a r hr).symm pq).hom
      infer_instance
    have : Epi fE := by dsimp [fE]; infer_instance
    have hfE : fE ≫ (E.page r hr).iCycles pq =
        inc ≫ filteredComplexPageπ K F r pq ≫ (e pq.1 pq.2 r hr).inv := by
      simp only [fE, Category.assoc, HomologicalComplex.cyclesMap_i, hai]
      simpa only [Category.assoc, inc] using
        congrArg (fun f ↦ f ≫ (e pq.1 pq.2 r hr).inv) hf
    have hsource := hc.successor r hr pq.1 pq.2 hZ _ (𝟙 _) fE
      (by simpa only [Category.id_comp] using hfE)
    have htarget := hc'.successor r hr pq.1 pq.2 hZ' _
      (g (r + 1) (by omega) pq)
      (fE ≫ HomologicalComplex.cyclesMap (n r hr) pq) (by
        rw [Category.assoc, HomologicalComplex.cyclesMap_i]
        rw [← Category.assoc, hfE, hn]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hm]
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫ filteredComplexPageπ K' F' r pq ≫
            (e' pq.1 pq.2 r hr).inv) hinc)
    apply (cancel_epi (fE ≫ (E.page r hr).homologyπ pq)).1
    apply (cancel_mono (e' pq.1 pq.2 (r + 1) (by omega)).hom).1
    calc
      ((fE ≫ (E.page r hr).homologyπ pq) ≫
          (HomologicalComplex.homologyMap (n r hr) pq ≫
            (E'.iso r (r + 1) pq rfl hr).hom)) ≫
          (e' pq.1 pq.2 (r + 1) (by omega)).hom =
          g (r + 1) (by omega) pq ≫ filteredComplexPageπ K' F' (r + 1) pq := by
        simpa only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc] using
          htarget
      _ = filteredComplexPageπ K F (r + 1) pq ≫ m (r + 1) (by omega) pq := by
        exact (hm (r + 1) (by omega) pq).symm
      _ = ((fE ≫ (E.page r hr).homologyπ pq) ≫
          ((E.iso r (r + 1) pq rfl hr).hom ≫ (n (r + 1) (by omega)).f pq)) ≫
          (e' pq.1 pq.2 (r + 1) (by omega)).hom := by
        rw [hn]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        simpa only [Category.assoc, Category.id_comp] using
          congrArg (fun f ↦ f ≫ m (r + 1) (by omega) pq) hsource.symm
  let N : E ⟶ E' :=
    { hom := n
      comm := by
        intro r r' pq hrr' hr
        subst r'
        exact hsucc r hr pq }
  refine ⟨N, ?_⟩
  intro A p q r hr x y z z' hxy hz hz'
  have hy : x ≫ (s p).f (p + q) = y := by
    apply (cancel_mono ((F'.step p).arrow.f (p + q))).1
    simpa only [Category.assoc, hsi] using hxy
  have hzg : z ≫ g r hr (p, q) = z' := by
    apply (cancel_mono (F'.complexCycles p (p + q) r).arrow).1
    exact (hrep r hr (p, q) A x z hz).trans (by rw [hy, hz'])
  change z ≫ filteredComplexPageπ K F r (p, q) ≫ (e p q r hr).inv ≫
      (n r hr).f (p, q) = _
  rw [hn]
  simp only [Iso.inv_hom_id_assoc, reassoc_of% hm]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ filteredComplexPageπ K' F' r (p, q) ≫
      (e' p q r hr).inv) hzg

end CategoryTheory
