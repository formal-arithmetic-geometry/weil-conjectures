/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups V2 and T3
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis
import Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.CategoryTheory.FilteredHomologyTowerDifferential
import all Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives
import Sheaf.CategoryTheory.FiniteCycleFormula
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Representative comparisons with the canonical exact-couple tower

Source: Stacks Project, Tags 012K and 011R.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem filtered_incoming_alpha
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (s : ℕ) (p q : ℤ) :
    (filteredHomologyExactCouple K F).incomingAlphaIter s (2 * p + q + 2) (-p - 1) ≍
      HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step (p + ((s : ℤ) + 1))) (F.step (p + 1))
          (F.antitone_step (by omega))) (p + q + 1) := by
  unfold BigradedExactCouple.incomingAlphaIter
  rw [comp_eqToHom_heq_iff]
  apply (filtered_alphaIter K F s _ _).trans
  exact inclusion_homology_heq K F _ _ _ _ _ _ (by omega) (by omega)
    (by omega) (by omega) (by omega)

private theorem quotient_homology_transport
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : C} (a : A ⟶ B) (b : B ⟶ D) (hab : a ≫ b = 0)
    (S : ShortComplex C) (eA : A ≅ S.X₁) (eB : B ≅ S.X₂) (eD : D ≅ S.X₃)
    (ha : a ≫ eB.hom = eA.hom ≫ S.f)
    (hb : b ≫ eD.hom = eB.hom ≫ S.g) :
    ∃ (e : kernel b ≅ S.cycles)
      (h : cokernel (kernel.lift b a hab) ≅ S.homology),
      e.hom ≫ S.iCycles = kernel.ι b ≫ eB.hom ∧
      cokernel.π (kernel.lift b a hab) ≫ h.hom = e.hom ≫ S.homologyπ := by
  let e := kernel.mapIso b S.g eB eD hb ≪≫ S.cyclesIsoKernel.symm
  have he : e.hom ≫ S.iCycles = kernel.ι b ≫ eB.hom := by
    simp [e, ShortComplex.cyclesIsoKernel]
  have hea : kernel.lift b a hab ≫ e.hom = eA.hom ≫ S.toCycles := by
    apply (cancel_mono S.iCycles).mp
    simp only [Category.assoc, he, kernel.lift_ι_assoc, ShortComplex.toCycles_i]
    exact ha
  let c := cokernel.mapIso (kernel.lift b a hab) S.toCycles eA e hea
  let d := (cokernelIsCokernel S.toCycles).coconePointUniqueUpToIso S.homologyIsCokernel
  refine ⟨e, c ≪≫ d, he, ?_⟩
  simp only [Iso.trans_hom, ← Category.assoc]
  simp only [c, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
  rw [Category.assoc]
  congr 1
  exact (cokernelIsCokernel S.toCycles).comp_coconePointUniqueUpToIso_hom
    S.homologyIsCokernel WalkingParallelPair.one

private theorem complex_homology_transport
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : C} (a : A ⟶ B) (b : B ⟶ D) (hab : a ≫ b = 0)
    {ι : Type*} {c : ComplexShape ι} (L : HomologicalComplex C c)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    (eA : A ≅ L.X i) (eB : B ≅ L.X j) (eD : D ≅ L.X k)
    (ha : a ≫ eB.hom = eA.hom ≫ L.d i j)
    (hb : b ≫ eD.hom = eB.hom ≫ L.d j k) :
    ∃ (e : kernel b ≅ L.cycles j)
      (h : cokernel (kernel.lift b a hab) ≅ L.homology j),
      e.hom ≫ L.iCycles j = kernel.ι b ≫ eB.hom ∧
      cokernel.π (kernel.lift b a hab) ≫ h.hom = e.hom ≫ L.homologyπ j := by
  obtain ⟨e, h, he, hh⟩ := quotient_homology_transport a b hab (L.sc' i j k)
    eA eB eD ha hb
  refine ⟨e ≪≫ (L.cyclesIsoSc' i j k hi hk).symm,
    h ≪≫ (L.homologyIsoSc' i j k hi hk).symm, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      HomologicalComplex.cyclesIsoSc'_inv_iCycles] using he
  · simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, hh, Category.assoc, HomologicalComplex.π_homologyIsoSc'_inv,
      ← Category.assoc]

private theorem epi_quotient_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : C} (b : A ⟶ B) (f : B ⟶ D) [Epi f]
    (hk : kernelSubobject f = imageSubobject b) :
    ∃ e : D ≅ cokernel b, f ≫ e.hom = cokernel.π b := by
  have hz : b ≫ f = 0 := by
    apply (kernelSubobject_factors_iff _ _).mp
    rw [hk]
    simpa only [Category.id_comp] using imageSubobject_factors_comp_self b (𝟙 _)
  have hc := ((ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk b f hz)).mpr
    hk.symm).gIsCokernel
  let e := hc.coconePointUniqueUpToIso (cokernelIsCokernel b)
  exact ⟨e, hc.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel b)
    WalkingParallelPair.one⟩

private theorem cycles_antitone
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p n : ℤ)
    {r t : ℤ} (hrt : r ≤ t) : F.complexCycles p n t ≤ F.complexCycles p n r := by
  unfold DecreasingFiltration.complexCycles
  apply (Subobject.«exists» _).monotone
  apply (Subobject.pullback _).monotone
  apply sup_le_sup_right
  apply inf_le_inf_left
  apply (Subobject.pullback _).monotone
  unfold DecreasingFiltration.complexStep
  have hF := F.antitone_step (show p + r ≤ p + t by omega)
  have hfac := congrArg (fun φ ↦ φ.f (n + 1)) (Subobject.ofLE_arrow hF)
  rw [HomologicalComplex.comp_f] at hfac
  apply imageSubobject_le _
    (((Subobject.ofLE _ _ hF).f (n + 1)) ≫
      factorThruImageSubobject ((F.step (p + r)).arrow.f (n + 1)))
  rw [Category.assoc, imageSubobject_arrow_comp, hfac]

private theorem graded_cycle_lifts
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    ∃ j : ∀ (s : ℕ) (p q : ℤ),
        (F.complexCycles p (p + q) (s + 1) : C) ⟶ (F.gradedPiece p).cycles (p + q),
      ∀ (s : ℕ) (p q : ℤ),
        j s p q ≫ (F.gradedPiece p).iCycles (p + q) =
          (F.complexCycles p (p + q) (s + 1)).arrow := by
  have hz (s : ℕ) (p q : ℤ) :
      (F.complexCycles p (p + q) (s + 1)).arrow ≫
          (F.gradedPiece p).d (p + q) (p + q + 1) = 0 := by
    apply (kernelSubobject_factors_iff _ _).mp
    apply Subobject.factors_of_le _
      ((cycles_antitone K F p (p + q) (show (1 : ℤ) ≤ s + 1 by omega)).trans_eq
        (F.filteredComplex_firstPage_cycles_boundaries p (p + q)).1)
    exact Subobject.factors_self _
  refine ⟨fun s p q ↦ (F.gradedPiece p).liftCycles _ (p + q + 1) (by simp) (hz s p q),
    fun s p q ↦ ?_⟩
  exact HomologicalComplex.liftCycles_i _ _ _ _ _

private theorem tower_cycle_lifts
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (j : ∀ (s : ℕ) (p q : ℤ),
      (F.complexCycles p (p + q) (s + 1) : C) ⟶ (F.gradedPiece p).cycles (p + q))
    (hj : ∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (F.gradedPiece p).iCycles (p + q) =
        (F.complexCycles p (p + q) (s + 1)).arrow) :
    ∃ t : ∀ (s : ℕ) (p q : ℤ),
        (F.complexCycles p (p + q) (s + 1) : C) ⟶
          ((filteredHomologyExactCouple K F).cycleBoundaryTower.Z s (2 * p + q) (-p) : C),
      ∀ (s : ℕ) (p q : ℤ),
        t s p q ≫
            ((filteredHomologyExactCouple K F).cycleBoundaryTower.Z s (2 * p + q) (-p)).arrow ≫
            (filteredHomologyEIso K F p q).hom =
          j s p q ≫ (F.gradedPiece p).homologyπ (p + q) := by
  sorry

set_option linter.unusedVariables false in
/-- Graded filtered cycles cover the canonical tower cycles, and their composites
with the tower projections have exactly the boundary kernels. This is only the
object and quotient comparison, without a differential assertion.
Source: Stacks Project, Tag 012K, cycle/boundary formulas in Lemma 12.24.2;
Tag 011R, the canonical derived-couple quotient construction.
(blueprint: lem-sp-filtered-homology-tower-quotients).

Proof. First construct j and t at every stage, before proving epimorphy.
Since r=s+1 is at least one, an r-cycle has zero graded differential;
its graded inclusion therefore factors uniquely through iCycles, defining j.
Compose j with graded homology and the inverse initial E identification.
The finiteCycle_formula identifies T.Z s with the inverse image, under the
initial connecting f, of the image of the s-fold incoming alpha. On an
r-cycle representative, the connecting class is represented by its differential
in F^(p+s+1); its inclusion into F^(p+1) is exactly that incoming alpha
iterate on homology. Thus the initial E class factors through T.Z s.
This calculation descends from the epic cycle-representative projection,
because the graded representative kernel maps to zero in initial homology.
Factor uniquely through the monic tower inclusion to define t, for every s.
This supplies the whole normalized family required by the differential lemma,
without assuming any quotient comparison or the epimorphy being proved.

Now induct on s for the epic projection composites and their kernels.
At zero, hH and epic cancellation identify the composite with the initial
cokernel projection followed by eH and the inverse initial E identification;
it is epic and has kernel B_1. At stage s, its cokernel universal property
identifies the page with Z_(s+1)/B_(s+1). Apply the tower differential lemma
to the already constructed families and cancel an epic representative cover
to identify the canonical differential with the representative differential.
Transport the resulting three-term complex along these page identifications.
The existing normalized-homology comparison packages the successor-cycle cover
and successor-boundary image calculations: it identifies the homology with
Z_(s+2)/B_(s+2), normalized on successor cycles. Its cokernel projection is
therefore epic and has exactly the successor-boundary kernel.
The tower cycleLift_comm and projection_succ equations identify that map
with t at stage s+1 followed by the tower projection: cancel the preceding
kernel inclusion and use the monic normalization of t to identify the lifts.
This proves both assertions at s+1. All representative lifts are made after
pullback along epimorphisms, so no projectivity or infinite sums are required.
The monic normalization fixes j and t uniquely; no arbitrary data is chosen. -/
theorem filteredHomology_tower_quotients
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
    (hH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
 :
    ∃ (j : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        (U.obj.filtration.gradedPiece p).cycles (p + q))
      (t : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
          s (2 * p + q) (-p) : C)),
      (∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
        (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow) ∧
      (∀ (s : ℕ) (p q : ℤ),
      t s p q ≫
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
            s (2 * p + q) (-p)).arrow ≫
          (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j s p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q)) ∧
      (∀ (s : ℕ) (p q : ℤ), Epi (t s p q ≫
          (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
            s (2 * p + q) (-p))) ∧
      (∀ (s : ℕ) (p q : ℤ), kernelSubobject (t s p q ≫
          (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
            s (2 * p + q) (-p)) =
        imageSubobject (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega)))) := by
  sorry

end CategoryTheory
