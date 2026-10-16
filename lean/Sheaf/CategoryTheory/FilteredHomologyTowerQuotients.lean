/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups V2 and T3
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis
import Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.CategoryTheory.FilteredHomologyTowerDifferential
import all Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives
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
  classical
  let X := filteredHomologyExactCouple K F
  let c (s : ℕ) (p q : ℤ) :=
    j s p q ≫ (F.gradedPiece p).homologyπ (p + q) ≫ (filteredHomologyEIso K F p q).inv
  have hc (s : ℕ) (p q : ℤ) :
      (X.cycleBoundaryTower.Z s (2 * p + q) (-p)).Factors (c s p q) := by
    rw [BigradedExactCouple.finiteCycle_formula]
    apply (pullback_factors_iff _ _ _).mpr
    obtain ⟨x, _, hxepi, _, hx, _⟩ :=
      F.filteredComplex_representative_epis p (p + q) (s + 1) (by omega)
    let R := F.complexCycleRepresentatives p (p + q) (s + 1)
    have hd : (F.complexStep (p + (s + 1)) (p + q + 1)).Factors
        (R.arrow ≫ (F.step p).arrow.f (p + q) ≫ K.d (p + q) (p + q + 1)) := by
      have hR := (pullback_factors_iff _ _ _).mp R.factors_self
      have hR' := Subobject.factors_right_of_inf_factors hR
      have hh := (pullback_factors_iff _ _ _).mp hR'
      simpa only [Category.assoc] using hh
    rw [DecreasingFiltration.complexStep, imageSubobject_mono] at hd
    obtain ⟨a', ha'⟩ := (Subobject.mk_factors_iff _ _).mp hd
    have hg : (x ≫ j s p q) ≫ (F.gradedPiece p).iCycles (p + q) =
        R.arrow ≫ (F.complexQuotientπ p (p + 1) (by omega)).f (p + q) := by
      rw [Category.assoc, hj]
      exact hx
    obtain ⟨z, _, hz⟩ := connecting_representative K F p (p + q) (s + 1) (by omega)
      R.arrow a' (x ≫ j s p q) ha'.symm hg
    have hrepr : x ≫ c s p q ≫ X.f (2 * p + q) (-p) =
        (z ≫ (F.step (p + (s + 1)) : CochainComplex C ℤ).homologyπ (p + q + 1) ≫
          eqToHom (by
            change (F.step (p + (s + 1)) : CochainComplex C ℤ).homology (p + q + 1) =
              (F.step (-(-p - 1 - s)) : CochainComplex C ℤ).homology
                (2 * p + q + 2 + s + (-p - 1 - s))
            apply congrArg₂ (fun a n ↦ (F.step a : CochainComplex C ℤ).homology n) <;>
              omega)) ≫ X.incomingAlphaIter s (2 * p + q + 2) (-p - 1) := by
      apply eq_of_heq
      dsimp only [c]
      simp only [Category.assoc]
      have htarget : X.D (2 * p + q + 2) (-p - 1) =
          (F.step (p + 1) : CochainComplex C ℤ).homology (p + q + 1) := by
        change (F.step (-(-p - 1)) : CochainComplex C ℤ).homology
          (2 * p + q + 2 + (-p - 1)) = _
        apply congrArg₂ (fun a n ↦ (F.step a : CochainComplex C ℤ).homology n) <;> omega
      have hleft := heq_comp rfl rfl htarget
        (f := x ≫ j s p q ≫ (F.gradedPiece p).homologyπ (p + q))
        HEq.rfl (filtered_initial_f K F p q)
      have hsource : (F.step (p + (s + 1)) : CochainComplex C ℤ).homology
          (p + q + 1) = X.D (2 * p + q + 2 + s) (-p - 1 - s) := by
        change _ = (F.step (-(-p - 1 - s)) : CochainComplex C ℤ).homology
          (2 * p + q + 2 + s + (-p - 1 - s))
        apply congrArg₂ (fun a n ↦ (F.step a : CochainComplex C ℤ).homology n) <;> omega
      have hright := heq_comp rfl rfl htarget
        (f := z ≫ (F.step (p + (s + 1)) : CochainComplex C ℤ).homologyπ (p + q + 1))
        HEq.rfl
        ((eqToHom_comp_heq _ hsource).trans (filtered_incoming_alpha K F s p q))
      have hz' := heq_of_eq hz
      simp only [Category.assoc] at hleft hright hz'
      exact hleft.trans (hz'.trans hright.symm)
    have hi : imageSubobject (c s p q ≫ X.f (2 * p + q) (-p)) ≤
        imageSubobject (X.incomingAlphaIter s (2 * p + q + 2) (-p - 1)) := by
      rw [← imageSubobject_comp_of_epi x, hrepr]
      exact imageSubobject_comp_le _ _
    exact (Subobject.imageSubobject_le_iff _ _).mp hi
  refine ⟨fun s p q ↦ Subobject.factorThru _ _ (hc s p q), fun s p q ↦ ?_⟩
  rw [← Category.assoc, Subobject.factorThru_arrow]
  simp [c]

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
  classical
  obtain ⟨j, hj⟩ := graded_cycle_lifts U.obj.obj U.obj.filtration
  obtain ⟨t, ht⟩ := tower_cycle_lifts U.obj.obj U.obj.filtration j hj
  let X := filteredHomologyExactCouple U.obj.obj U.obj.filtration
  let Q (s : ℕ) (p q : ℤ) := t s p q ≫ X.cycleBoundaryTower.projection s (2 * p + q) (-p)
  have h : ∀ s : ℕ,
      (∀ p q : ℤ, Epi (Q s p q)) ∧
      (∀ p q : ℤ, kernelSubobject (Q s p q) =
        imageSubobject (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega)))) := by
    intro s
    induction s with
    | zero =>
      have hbase (p q : ℤ) : Q 0 p q =
          cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom ≫ (filteredHomologyEIso U.obj.obj U.obj.filtration p q).inv := by
        apply (cancel_mono (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom).mp
        dsimp only [Q]
        rw [X.cycleBoundaryTower.projection_zero]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [ht]
        obtain ⟨z, g, hz, hg, hzEpi, hnorm⟩ := hH U p q
        have hjg : z ≫ j 0 p q = g := by
          apply (cancel_mono ((U.obj.filtration.gradedPiece p).iCycles (p + q))).mp
          rw [Category.assoc, hj]
          exact hz.trans hg.symm
        apply (cancel_epi z).mp
        simpa only [← Category.assoc, hjg] using hnorm.symm
      constructor
      · intro p q
        rw [hbase]
        infer_instance
      · intro p q
        rw [hbase, kernelSubobject_comp_mono]
        exact ((ShortComplex.exact_iff_image_eq_kernel _).mp
          (ShortComplex.exact_cokernel
            (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))))).symm
    | succ s ih =>
      have hQepi (p q : ℤ) : Epi (Q s p q) := ih.1 p q
      have heQ (p q : ℤ) := epi_quotient_iso
        (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega))) (Q s p q) (ih.2 p q)
      choose e he using heQ
      obtain ⟨D, _, _⟩ := filteredComplex_page_differential_exists_unique
        U.obj.obj U.obj.filtration (s + 1) (by omega)
      have hd (p q : ℤ) :
          (e p q).hom ≫ D.d (p, q) (p + (s + 1), q - (s + 1) + 1) =
            (X.pageCouple s).d (2 * p + q) (-p) ≫
              eqToHom (congrArg₂ (X.pageCouple s).E
                (show 2 * p + q + 2 + s =
                  2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
                (show -p - 1 - s = -(p + (s + 1)) by omega)) ≫
              (e (p + (s + 1)) (q - (s + 1) + 1)).hom := by
        let i : ℤ × ℤ := (p, q)
        let k : ℤ × ℤ := (p + (s + 1), q - (s + 1) + 1)
        have hik : (ComplexShape.up' ((s : ℤ) + 1, 1 - ((s : ℤ) + 1))).Rel i k := by
          apply Prod.ext
          · rfl
          · dsimp [i, k]
            omega
        obtain ⟨A, a, a', x, y, hxEpi, ha, hx, hy⟩ :=
          filteredComplex_differential_representatives_cover U.obj.obj U.obj.filtration
            (s + 1) i k hik
        apply (cancel_epi (x ≫ Q s p q)).mp
        have hd := filteredHomology_tower_differential C hBZ eH hH U j t hj ht
          s p q A a a' x y ha hx hy
        have hD := D.on_representatives A i k hik a a' x y ha hx hy
        simp only [Category.assoc]
        rw [← Category.assoc (Q s p q), he]
        rw [show cokernel.π (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega))) =
          filteredComplexPageπ U.obj.obj U.obj.filtration (s + 1) i from rfl]
        rw [hD]
        have hd' : x ≫ Q s p q ≫
            (X.pageCouple s).d (2 * p + q) (-p) ≫
            eqToHom (congrArg₂ (X.pageCouple s).E
              (show 2 * p + q + 2 + s =
                2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
              (show -p - 1 - s = -(p + (s + 1)) by omega)) = y ≫ Q s k.1 k.2 := by
          simpa only [Q, Category.assoc] using hd
        simpa only [Category.assoc, he, filteredComplexPageπ, filteredComplexPageObject,
          k, Prod.fst, Prod.snd] using
          congrArg (fun f ↦ f ≫ (e k.1 k.2).hom) hd'.symm
      have hsucc (p q : ℤ) :
          Epi (Q (s + 1) p q) ∧ kernelSubobject (Q (s + 1) p q) =
            imageSubobject (Subobject.ofLE _ _ (hBZ U p q (s + 1 + 1) (by omega))) := by
        let r : ℤ := s + 1
        let P := 2 * p + q
        let W := -p
        let Y := X.pageCouple s
        let i : ℤ × ℤ := (p - r, q + r - 1)
        let k : ℤ × ℤ := (p + r, q - r + 1)
        have hi : (ComplexShape.up' (r, 1 - r)).prev (p, q) = i := by
          apply ComplexShape.prev_eq'
          apply Prod.ext <;> dsimp [i] <;> omega
        have hk : (ComplexShape.up' (r, 1 - r)).next (p, q) = k := by
          apply ComplexShape.next_eq'
          apply Prod.ext <;> dsimp [k]; omega
        let eA : Y.E (P - s - 2) (W + s + 1) ≅ D.page.X i :=
          eqToIso (congrArg₂ Y.E
            (show P - s - 2 = 2 * i.1 + i.2 by dsimp [P, i, r]; omega)
            (show W + s + 1 = -i.1 by dsimp [W, i, r]; omega)) ≪≫ e i.1 i.2
        let eB : Y.E P W ≅ D.page.X (p, q) := e p q
        let eD : Y.E (P + 2 + s) (W - 1 - s) ≅ D.page.X k :=
          eqToIso (congrArg₂ Y.E
            (show P + 2 + s = 2 * k.1 + k.2 by dsimp [P, k, r]; omega)
            (show W - 1 - s = -k.1 by dsimp [W, k, r]; omega)) ≪≫ e k.1 k.2
        have hOut : Y.d P W ≫ eD.hom = eB.hom ≫ D.page.d (p, q) k := by
          exact (hd p q).symm
        have hIn : Y.dInto P W ≫ eB.hom = eA.hom ≫ D.page.d i (p, q) := by
          have h1 : i.1 + ((s : ℤ) + 1) = p := by dsimp [i, r]; omega
          have h2 : i.2 - ((s : ℤ) + 1) + 1 = q := by dsimp [i, r]; omega
          have h3 : 2 * i.1 + i.2 = P - s - 2 := by dsimp [i, r, P]; omega
          have h4 : -i.1 = W + s + 1 := by dsimp [i, r, W]; omega
          have transport (a b p' q' : ℤ)
              (hp : a + ((s : ℤ) + 1) = p') (hq : b - ((s : ℤ) + 1) + 1 = q') :
              (e a b).hom ≫ D.d (a, b) (p', q') =
                Y.d (2 * a + b) (-a) ≫ eqToHom (congrArg₂ Y.E
                  (show 2 * a + b + 2 + s = 2 * p' + q' by omega)
                  (show -a - 1 - s = -p' by omega)) ≫ (e p' q').hom := by
            subst p' q'
            exact hd a b
          have hh := transport i.1 i.2 p q h1 h2
          have hdd : Y.dInto P W ≍
              Y.d (2 * i.1 + i.2) (-i.1) ≫ eqToHom (congrArg₂ Y.E
                (show 2 * i.1 + i.2 + 2 + s = 2 * p + q by omega)
                (show -i.1 - 1 - s = -p by omega)) := by
            unfold BigradedExactCouple.dInto
            simp only [comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
            congr! 1 <;> omega
          have hc := heq_comp (congrArg₂ Y.E h3.symm h4.symm) rfl rfl
            hdd (HEq.rfl : (e p q).hom ≍ (e p q).hom)
          simp only [Category.assoc] at hc
          have hf := hc.trans (heq_of_eq hh.symm)
          have hf' := (heq_eqToHom_comp_iff
            ((e i.1 i.2).hom ≫ D.d (i.1, i.2) (p, q))
            (Y.dInto P W ≫ (e p q).hom)
            (congrArg₂ Y.E h3.symm h4.symm)).mpr hf
          have hf'' := eq_of_heq hf'
          simpa only [eA, eB, Iso.trans_hom, eqToIso, Category.assoc,
            FilteredComplexPageDifferential.page, filteredComplexPageObject] using hf''
        -- Compare the canonical derived quotient with concrete page homology.
        obtain ⟨ec, eh, hec, heh⟩ := complex_homology_transport
          (Y.dInto P W) (Y.d P W) (Y.dInto_comp_d P W) D.page
          i (p, q) k hi hk eA eB eD hIn hOut
        have hZ := cycles_antitone U.obj.obj U.obj.filtration p (p + q)
          (show (s : ℤ) + 1 ≤ (s + 1 : ℕ) + 1 by omega)
        have hjinc : Subobject.ofLE _ _ hZ ≫ j s p q = j (s + 1) p q := by
          apply (cancel_mono ((U.obj.filtration.gradedPiece p).iCycles (p + q))).mp
          rw [Category.assoc, hj, hj, Subobject.ofLE_arrow]
        have htinc : t (s + 1) p q ≫ Subobject.ofLE _ _
            (X.cycleBoundaryTower.Z_decreasing s P W) =
              Subobject.ofLE _ _ hZ ≫ t s p q := by
          apply (cancel_mono (X.cycleBoundaryTower.Z s P W).arrow).mp
          apply (cancel_mono (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom).mp
          simp only [Category.assoc, Subobject.ofLE_arrow]
          rw [ht]
          simpa only [← Category.assoc, hjinc] using
            congrArg (fun f ↦ Subobject.ofLE _ _ hZ ≫ f) (ht s p q).symm
        let l := t (s + 1) p q ≫ X.cycleBoundaryTower.cycleLift s P W
        have hl : l ≫ kernel.ι (Y.d P W) = Subobject.ofLE _ _ hZ ≫ Q s p q := by
          dsimp only [l, Q]
          rw [Category.assoc, X.cycleBoundaryTower.cycleLift_comm,
            ← Category.assoc, htinc, Category.assoc]
        have hlf : (l ≫ ec.hom) ≫ D.page.iCycles (p, q) =
            Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ
              U.obj.obj U.obj.filtration r (p, q) := by
          rw [Category.assoc, hec, ← Category.assoc, hl, Category.assoc, he]
          rfl
        obtain ⟨en, hn, _⟩ := filteredComplex_normalized_homology
          U.obj.obj U.obj.filtration r (by dsimp [r]; omega) D (p, q)
        have hn' := hn hZ (l ≫ ec.hom) hlf
        have hnorm : Q (s + 1) p q ≫ (eh ≪≫ en).hom =
            cokernel.π (Subobject.ofLE _ _ (hBZ U p q (s + 1 + 1) (by omega))) := by
          dsimp only [Q]
          rw [X.cycleBoundaryTower.projection_succ]
          rw [← Category.assoc]
          change (l ≫ Y.derivedEProjection P W) ≫ (eh ≪≫ en).hom = _
          simp only [Iso.trans_hom, Category.assoc]
          rw [← Category.assoc (Y.derivedEProjection P W),
            show Y.derivedEProjection P W ≫ eh.hom =
            ec.hom ≫ D.page.homologyπ (p, q) from heh]
          simpa only [Category.assoc, filteredComplexPageπ, r,
            Nat.cast_add, Nat.cast_one] using hn'
        have hQ : Q (s + 1) p q =
            cokernel.π (Subobject.ofLE _ _ (hBZ U p q (s + 1 + 1) (by omega))) ≫
              (eh ≪≫ en).inv := by
          apply (cancel_mono (eh ≪≫ en).hom).mp
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
          exact hnorm
        have hEpi : Epi (Q (s + 1) p q) := by
          rw [hQ]
          infer_instance
        refine ⟨hEpi, ?_⟩
        have hK := congrArg (fun f ↦ kernelSubobject f) hnorm
        simp only [kernelSubobject_comp_mono] at hK
        exact hK.trans (((ShortComplex.exact_iff_image_eq_kernel _).mp
          (ShortComplex.exact_cokernel
            (Subobject.ofLE _ _ (hBZ U p q (s + 1 + 1) (by omega))))).symm)
      exact ⟨fun p q ↦ (hsucc p q).1, fun p q ↦ (hsucc p q).2⟩
  exact ⟨j, t, hj, ht, fun s ↦ (h s).1, fun s ↦ (h s).2⟩

end CategoryTheory
