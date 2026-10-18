/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups V2, T3 and M6
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import Sheaf.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.CategoryTheory.FilteredHomologyTowerDifferential
import Sheaf.CategoryTheory.FilteredHomologyCoupleComputations
import all Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives
import Sheaf.CategoryTheory.FiniteCycleFormula

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

private theorem factors_of_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : C} (S : Subobject D) (f : B ⟶ D) (π : A ⟶ B) [Epi π]
    (h : S.Factors (π ≫ f)) : S.Factors f := by
  have hz : f ≫ cokernel.π S.arrow = 0 := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, ← S.factorThru_arrow (π ≫ f) h, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  rw [← Abelian.monoLift_comp S.arrow f hz]
  exact Subobject.factors_comp_arrow _

/-- The normalized maps from filtered cycles into the canonical cycle tower.
Source: Stacks Project, Tags 012K and 011R.
(blueprint: lem-sp-filtered-homology-tower-quotients).

The connecting representative calculation factors the initial homology class
through the finite-cycle pullback and then through the monic tower inclusion.
This gives the stated normalized family. -/
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
  let X := filteredHomologyExactCouple K F
  let T := X.cycleBoundaryTower
  let φ (s : ℕ) (p q : ℤ) := j s p q ≫ (F.gradedPiece p).homologyπ (p + q) ≫
    (filteredHomologyEIso K F p q).inv
  have hfac (s : ℕ) (p q : ℤ) : (T.Z s (2 * p + q) (-p)).Factors (φ s p q) := by
    rw [BigradedExactCouple.finiteCycle_formula]
    apply pullback_factors
    obtain ⟨A, a, a', x, y, hxepi, ha, hx, hy⟩ :=
      filteredComplex_differential_representatives_cover K F (s + 1)
        (p, q) (p + (s + 1), q - (s + 1) + 1) (by
          change (p, q) + ((s : ℤ) + 1, 1 - ((s : ℤ) + 1)) = _
          exact Prod.ext (by rfl) (by dsimp; omega))
    have : Epi x := hxepi
    apply factors_of_epi _ _ x
    let p' := p + (s + 1)
    let q' := q - (s + 1) + 1
    let n' := p' + q'
    have hn : p + q + 1 = n' := by dsimp [n', p', q']; omega
    have hda' : a' ≫ (F.step p' : CochainComplex C ℤ).d n' (n' + 1) = 0 := by
      apply (cancel_mono ((F.step p').arrow.f (n' + 1))).mp
      rw [Category.assoc, ← (F.step p').arrow.comm]
      rw [← Category.assoc a', ← ha]
      simp only [n', p', q', Category.assoc, K.d_comp_d, comp_zero, zero_comp]
    let b := (F.step p' : CochainComplex C ℤ).liftCycles
      (i := n') a' (n' + 1) (by simp) hda'
    have hb : b ≫ (F.step p' : CochainComplex C ℤ).iCycles n' = a' := by
      simp only [b, HomologicalComplex.liftCycles_i]
    have hδ := connecting_from_cycle K F p (p + q) (s + 1) n' (by omega) hn
      a b (x ≫ j s p q)
      (by rw [← Category.assoc b, hb]; exact ha)
      (by rw [Category.assoc, hj]; exact hx)
    let eA : (F.step p' : CochainComplex C ℤ).homology n' ≅
        X.D (2 * p + q + 2 + s) (-p - 1 - s) := eqToIso (by
      rw [(filteredHomologyExactCouple_computations K F).1]
      apply congrArg₂ (fun a n ↦ (F.step a : CochainComplex C ℤ).homology n)
      · dsimp [p']; omega
      · dsimp [n', p', q']; omega)
    let eD : X.D (2 * p + q + 2) (-p - 1) ≅
        (F.step (p + 1) : CochainComplex C ℤ).homology n' := eqToIso (by
      rw [(filteredHomologyExactCouple_computations K F).1]
      apply congrArg₂ (fun a n ↦ (F.step a : CochainComplex C ℤ).homology n)
      · omega
      · dsimp [n', p', q']; omega)
    have hf : (filteredHomologyEIso K F p q).inv ≫
        X.f (2 * p + q) (-p) ≫ eD.hom =
          (filteredStep_shortExact K F p).δ (p + q) n' (by
            simp [ComplexShape.up]; omega) := by
      apply eq_of_heq
      simp only [eD, eqToIso.hom, ← Category.assoc, comp_eqToHom_heq_iff]
      exact (filtered_initial_f K F p q).trans
        (connecting_index_heq K F p (p + q) n' hn)
    have hα : eA.hom ≫ X.incomingAlphaIter s (2 * p + q + 2) (-p - 1) ≫ eD.hom =
        HomologicalComplex.homologyMap
          (Subobject.ofLE (F.step p') (F.step (p + 1))
            (F.antitone_step (by dsimp [p']; omega))) n' := by
      apply eq_of_heq
      simp only [eA, eD, eqToIso.hom, ← Category.assoc, comp_eqToHom_heq_iff,
        eqToHom_comp_heq_iff]
      exact (filtered_incoming_alpha K F s p q).trans
        (inclusion_homology_heq K F _ _ _ _ _ _ (by omega)
          (by dsimp [p']; omega) (by rfl) (by rfl)
          (by dsimp [n', p', q']; omega))
    have heq : x ≫ φ s p q ≫ X.f (2 * p + q) (-p) =
        (b ≫ (F.step p' : CochainComplex C ℤ).homologyπ n' ≫ eA.hom) ≫
          X.incomingAlphaIter s (2 * p + q + 2) (-p - 1) := by
      apply (cancel_mono eD.hom).mp
      simp only [φ, Category.assoc]
      rw [hf, hα]
      simpa only [Category.assoc] using hδ
    rw [heq]
    exact imageSubobject_factors_comp_self _ _
  refine ⟨fun s p q ↦ (T.Z s (2 * p + q) (-p)).factorThru (φ s p q) (hfac s p q),
    fun s p q ↦ ?_⟩
  rw [← Category.assoc, Subobject.factorThru_arrow]
  simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem quotient_incoming_transport
    {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}
    (Y : BigradedExactCouple C s) {c : ComplexShape (ℤ × ℤ)}
    (L : HomologicalComplex C c)
    (e : ∀ p q : ℤ, Y.E (2 * p + q) (-p) ≅ L.X (p, q))
    (hd : ∀ p q : ℤ,
      (e p q).hom ≫ L.d (p, q) (p + (s + 1), q - (s + 1) + 1) =
        Y.d (2 * p + q) (-p) ≫ eqToHom (congrArg₂ Y.E (by omega) (by omega)) ≫
          (e (p + (s + 1)) (q - (s + 1) + 1)).hom)
    (a b p q : ℤ) (hp : a + (s + 1) = p) (hq : b - (s + 1) + 1 = q) :
    Y.dInto (2 * p + q) (-p) ≫ (e p q).hom =
      eqToHom (congrArg₂ Y.E
        (show 2 * p + q - s - 2 = 2 * a + b by omega)
        (show -p + s + 1 = -a by omega)) ≫ (e a b).hom ≫ L.d (a, b) (p, q) := by
  subst p q
  rw [hd]
  have hnat := eqToHom_naturality (fun pq : ℤ × ℤ ↦ Y.d pq.1 pq.2)
    (show (2 * (a + (s + 1)) + (b - (s + 1) + 1) - s - 2,
        -(a + (s + 1)) + s + 1) = (2 * a + b, -a) by ext <;> omega)
  simp only [BigradedExactCouple.dInto, ← Category.assoc]
  rw [← hnat]
  simp only [Category.assoc, eqToHom_trans]

/-- Quotient induction for the normalized tower maps.
Source: Stacks Project, Tag 012K, Lemma 12.24.2.
(blueprint: lem-sp-filtered-homology-tower-quotients).

Induction on the canonical tower identifies each page projection with the
cokernel of the displayed boundary inclusion.  Exactness and the normalized
homology comparison give the epimorphy and the kernel formula. -/
private theorem tower_quotient_properties
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (_hr : 1 ≤ r),
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
    (j : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        (U.obj.filtration.gradedPiece p).cycles (p + q))
    (t : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
          s (2 * p + q) (-p) : C))
    (hj : ∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
        (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow)
    (ht : ∀ (s : ℕ) (p q : ℤ),
      t s p q ≫
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
            s (2 * p + q) (-p)).arrow ≫
          (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j s p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q)) :
    (∀ (s : ℕ) (p q : ℤ), Epi (t s p q ≫
          (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
            s (2 * p + q) (-p))) ∧
      (∀ (s : ℕ) (p q : ℤ), kernelSubobject (t s p q ≫
          (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
            s (2 * p + q) (-p)) =
        imageSubobject (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega)))) := by
  let F := U.obj.filtration
  let T := (filteredHomologyExactCouple U.obj.obj F).cycleBoundaryTower
  have hzero (p q : ℤ) :
      Epi (t 0 p q ≫ T.projection 0 (2 * p + q) (-p)) ∧
      kernelSubobject (t 0 p q ≫ T.projection 0 (2 * p + q) (-p)) =
        imageSubobject (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) := by
    obtain ⟨z, g, hz, hg, hepi, hcomp⟩ := hH U p q
    have : Epi z := hepi
    have hzj : z ≫ j 0 p q = g := by
      apply (cancel_mono ((F.gradedPiece p).iCycles (p + q))).mp
      rw [Category.assoc, hj]
      exact hz.trans hg.symm
    have hπ : cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
        (eH U p q).hom = j 0 p q ≫ (F.gradedPiece p).homologyπ (p + q) := by
      apply (cancel_epi z).mp
      simpa only [← Category.assoc, hzj] using hcomp
    have hQ : t 0 p q ≫ T.projection 0 (2 * p + q) (-p) =
        cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
          (eH U p q).hom ≫ (filteredHomologyEIso U.obj.obj F p q).inv := by
      apply (cancel_mono (filteredHomologyEIso U.obj.obj F p q).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [T.projection_zero]
      exact (ht 0 p q).trans hπ.symm
    rw [hQ]
    constructor
    · infer_instance
    · rw [kernelSubobject_comp_mono]
      exact ((ShortComplex.exact_iff_image_eq_kernel _).mp
        (ShortComplex.exact_cokernel
          (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))))).symm
  have hall (s : ℕ) : ∀ p q : ℤ,
      Epi (t s p q ≫ T.projection s (2 * p + q) (-p)) ∧
      kernelSubobject (t s p q ≫ T.projection s (2 * p + q) (-p)) =
        imageSubobject (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega))) := by
    induction s with
    | zero => exact hzero
    | succ s ih =>
      let Y := (filteredHomologyExactCouple U.obj.obj F).pageCouple s
      have hEpi (p q : ℤ) : Epi (t s p q ≫ T.projection s (2 * p + q) (-p)) :=
        (ih p q).1
      have hQuot (p q : ℤ) : ∃ e : Y.E (2 * p + q) (-p) ≅
          filteredComplexPageObject U.obj.obj F (s + 1) (p, q),
          (t s p q ≫ T.projection s (2 * p + q) (-p)) ≫ e.hom =
            filteredComplexPageπ U.obj.obj F (s + 1) (p, q) := by
        exact epi_quotient_iso (Subobject.ofLE _ _ (hBZ U p q (s + 1) (by omega)))
          (t s p q ≫ T.projection s (2 * p + q) (-p)) (ih p q).2
      choose e he using hQuot
      obtain ⟨D, _, _⟩ := filteredComplex_page_differential_exists_unique U.obj.obj F
        (s + 1) (by omega)
      have hd (p q : ℤ) :
          (e p q).hom ≫ D.d (p, q) (p + (s + 1), q - (s + 1) + 1) =
            Y.d (2 * p + q) (-p) ≫
              eqToHom (congrArg₂ Y.E
                (show 2 * p + q + 2 + s =
                  2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
                (show -p - 1 - s = -(p + (s + 1)) by omega)) ≫
              (e (p + (s + 1)) (q - (s + 1) + 1)).hom := by
        obtain ⟨A, a, a', x, y, hxepi, ha, hx, hy⟩ :=
          filteredComplex_differential_representatives_cover U.obj.obj F (s + 1)
            (p, q) (p + (s + 1), q - (s + 1) + 1) (by
              change (p, q) + ((s : ℤ) + 1, 1 - ((s : ℤ) + 1)) = _
              exact Prod.ext (by rfl) (by dsimp; omega))
        have : Epi x := hxepi
        apply (cancel_epi (x ≫ t s p q ≫ T.projection s (2 * p + q) (-p))).mp
        have hrep := filteredHomology_tower_differential C hBZ eH hH U j t hj ht
          s p q A a a' x y ha hx hy
        have hD := D.on_representatives A (p, q)
          (p + (s + 1), q - (s + 1) + 1) (by
            change (p, q) + ((s : ℤ) + 1, 1 - ((s : ℤ) + 1)) = _
            exact Prod.ext (by rfl) (by dsimp; omega)) a a' x y ha hx hy
        calc
          _ = y ≫ filteredComplexPageπ U.obj.obj F (s + 1)
              (p + (s + 1), q - (s + 1) + 1) := by
            simpa only [Category.assoc, reassoc_of% (he p q)] using hD
          _ = _ := by
            rw [← he]
            simpa only [Category.assoc] using
              congrArg (fun f ↦ f ≫ (e (p + (s + 1)) (q - (s + 1) + 1)).hom)
                hrep.symm
      intro p q
      let i : ℤ × ℤ := (p - (s + 1), q + (s + 1) - 1)
      let k : ℤ × ℤ := (p + (s + 1), q - (s + 1) + 1)
      let P := 2 * p + q
      let Q := -p
      let eA : Y.E (P - s - 2) (Q + s + 1) ≅ D.page.X i :=
        eqToIso (congrArg₂ Y.E (by dsimp [P, i]; omega)
          (by dsimp [Q, i]; omega)) ≪≫ e i.1 i.2
      let eB : Y.E P Q ≅ D.page.X (p, q) := e p q
      let eD : Y.E (P + 2 + s) (Q - 1 - s) ≅ D.page.X k :=
        eqToIso (congrArg₂ Y.E (by dsimp [P, k]; omega)
          (by dsimp [Q, k]; omega)) ≪≫ e k.1 k.2
      have ha : Y.dInto P Q ≫ eB.hom = eA.hom ≫ D.page.d i (p, q) := by
        simpa only [eA, eB, P, Q, Iso.trans_hom, eqToIso.hom, Category.assoc] using
          quotient_incoming_transport Y D.page e
            (fun a b ↦ hd a b) i.1 i.2 p q
            (by dsimp [i]; omega) (by dsimp [i]; omega)
      have hb : Y.d P Q ≫ eD.hom = eB.hom ≫ D.page.d (p, q) k := by
        simpa only [eB, eD, P, Q, k, FilteredComplexPageDifferential.page,
          Iso.trans_hom, eqToIso.hom, Category.assoc] using
          (hd p q).symm
      obtain ⟨eZ, eH', heZ, heH⟩ := complex_homology_transport
        (Y.dInto P Q) (Y.d P Q) (Y.dInto_comp_d P Q) D.page i (p, q) k
        ((ComplexShape.up' ((s : ℤ) + 1, 1 - ((s : ℤ) + 1))).prev_eq' (by
          change i + ((s : ℤ) + 1, 1 - ((s : ℤ) + 1)) = (p, q)
          ext <;> dsimp [i] <;> omega))
        ((ComplexShape.up' ((s : ℤ) + 1, 1 - ((s : ℤ) + 1))).next_eq' (by
          change (p, q) + ((s : ℤ) + 1, 1 - ((s : ℤ) + 1)) = k
          dsimp [k]
          exact Prod.ext (by rfl) (by omega)))
        eA eB eD ha hb
      obtain ⟨h, hn, _⟩ := filteredComplex_normalized_homology
        U.obj.obj F (s + 1) (by omega) D (p, q)
      have hZ : F.complexCycles p (p + q) (((s + 1 : ℕ) : ℤ) + 1) ≤
          F.complexCycles p (p + q) ((s : ℤ) + 1) :=
        cycles_antitone U.obj.obj F p (p + q) (by omega)
      have hjtrans : Subobject.ofLE _ _ hZ ≫ j s p q = j (s + 1) p q := by
        apply (cancel_mono ((F.gradedPiece p).iCycles (p + q))).mp
        simp only [F, Category.assoc, hj, Subobject.ofLE_arrow]
      have htrans : t (s + 1) p q ≫ Subobject.ofLE _ _ (T.Z_decreasing s P Q) =
          Subobject.ofLE _ _ hZ ≫ t s p q := by
        apply (cancel_mono (T.Z s P Q).arrow).mp
        apply (cancel_mono (filteredHomologyEIso U.obj.obj F p q).hom).mp
        calc
          _ = j (s + 1) p q ≫ (F.gradedPiece p).homologyπ (p + q) := by
            simpa only [Category.assoc, Subobject.ofLE_arrow_assoc] using ht (s + 1) p q
          _ = _ := by
            rw [← hjtrans]
            simpa only [Category.assoc] using
              congrArg (fun f ↦ Subobject.ofLE _ _ hZ ≫ f) (ht s p q).symm
      let m := t (s + 1) p q ≫ T.cycleLift s P Q
      have hm : m ≫ eZ.hom ≫ D.page.iCycles (p, q) =
          Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ U.obj.obj F (s + 1) (p, q) := by
        dsimp only [FilteredComplexPageDifferential.page] at ⊢ heZ
        rw [heZ]
        dsimp only [m, eB]
        simp only [Category.assoc]
        rw [reassoc_of% (T.cycleLift_comm s P Q), ← Category.assoc, htrans]
        simpa only [Category.assoc] using congrArg (fun f ↦ Subobject.ofLE _ _ hZ ≫ f)
          (he p q)
      have hn' : (m ≫ eZ.hom) ≫ D.page.homologyπ (p, q) ≫ h.hom =
          filteredComplexPageπ U.obj.obj F ((s : ℤ) + 1 + 1) (p, q) := by
        exact hn hZ (m ≫ eZ.hom) (by rw [Category.assoc]; exact hm)
      let eNext :
          ((filteredHomologyExactCouple U.obj.obj F).pageCouple (s + 1)).E P Q ≅
            filteredComplexPageObject U.obj.obj F ((s : ℤ) + 1 + 1) (p, q) :=
        eH' ≪≫ h
      have hNext : (t (s + 1) p q ≫ T.projection (s + 1) P Q) ≫ eNext.hom =
          filteredComplexPageπ U.obj.obj F ((s : ℤ) + 1 + 1) (p, q) := by
        dsimp only [eNext, Iso.trans_hom, BigradedExactCouple.pageCouple,
          BigradedExactCouple.derived]
        rw [T.projection_succ]
        simpa only [m, Y, Category.assoc, BigradedExactCouple.derivedEProjection] using
          (congrArg (fun f ↦ m ≫ f ≫ h.hom) heH).trans
            (by simpa only [Category.assoc] using hn')
      have hepi' : Epi (t (s + 1) p q ≫ T.projection (s + 1) P Q) := by
        have hπepi : Epi (filteredComplexPageπ U.obj.obj F ((s : ℤ) + 1 + 1) (p, q)) := by
          unfold filteredComplexPageπ
          infer_instance
        have : Epi ((t (s + 1) p q ≫ T.projection (s + 1) P Q) ≫ eNext.hom) := by
          rw [hNext]
          infer_instance
        have hfac : ((t (s + 1) p q ≫ T.projection (s + 1) P Q) ≫ eNext.hom) ≫
            eNext.inv = t (s + 1) p q ≫ T.projection (s + 1) P Q := by simp
        rw [← hfac]
        infer_instance
      refine ⟨hepi', ?_⟩
      have hk := congrArg (fun f ↦ kernelSubobject f) hNext
      rw [kernelSubobject_comp_mono] at hk
      refine hk.trans ?_
      exact ((ShortComplex.exact_iff_image_eq_kernel _).mp
        (ShortComplex.exact_cokernel
          (Subobject.ofLE _ _ (hBZ U p q ((s : ℤ) + 1 + 1) (by omega))))).symm
  exact ⟨fun s p q ↦ (hall s p q).1, fun s p q ↦ (hall s p q).2⟩

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
  obtain ⟨j, hj⟩ := graded_cycle_lifts U.obj.obj U.obj.filtration
  obtain ⟨t, ht⟩ := tower_cycle_lifts U.obj.obj U.obj.filtration j hj
  obtain ⟨hepi, hker⟩ := tower_quotient_properties
    C hBZ eH hH U j t hj ht
  exact ⟨j, t, hj, ht, hepi, hker⟩

end CategoryTheory
