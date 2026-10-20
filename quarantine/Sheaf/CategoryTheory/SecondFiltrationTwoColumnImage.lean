/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import all WeilConjectures.CategoryTheory.SecondFiltrationRowGradedCycles
import all WeilConjectures.CategoryTheory.SecondFiltrationRowCohomology
import all WeilConjectures.CategoryTheory.SecondFiltrationRowCycleComparison
import WeilConjectures.Algebra.Homology.ExactCouple.FirstQuadrant
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import Sheaf.CategoryTheory.FilteredComplexQuotientComponents
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis
import all Sheaf.CategoryTheory.FilteredQuotientComparisons
import all Sheaf.CategoryTheory.FilteredQuotientMapRestrictions

/-! # The two-column cohomology image

Source: Stacks Project, Homology, Tag 0130, Lemma 12.25.1, clauses (2), (4), (6).
(blueprint: lem-sp-second-filtration-two-column-image).
-/

@[expose] public section

universe u v uI

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
private theorem column_graded_terms
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ k : ℤ, k < 0 → IsZero (I.X k))
    (L : DecreasingFiltration (HomologicalComplex₂.total
      (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      (HomologicalComplex₂.secondFiltration
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) n).step p)
    (p : ℕ) :
    let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
      ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    let R := I.flip.X p
    ∃ a : ∀ q : ℤ, R.X q ⟶ (L.step (p : ℤ) : CochainComplex C ℤ).X ((p : ℤ) + q),
      (∀ q, a q ≫ (L.step (p : ℤ)).arrow.f ((p : ℤ) + q) =
        ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
          J.ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) (by
            change q + (p : ℤ) = (p : ℤ) + q; omega)) ∧
      (∀ q, IsIso (a q ≫
        (L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f ((p : ℤ) + q))) ∧
      (∀ q, (a q ≫
        (L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f ((p : ℤ) + q)) ≫
          (L.gradedPiece (p : ℤ)).d ((p : ℤ) + q) ((p : ℤ) + (q + 1)) =
        R.d q (q + 1) ≫ (a (q + 1) ≫
          (L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f
            ((p : ℤ) + (q + 1)))) := by
  classical
  let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
  let R := I.flip.X p
  have hterms (q : ℤ) : ∃ a : R.X q ⟶
      (L.step (p : ℤ) : CochainComplex C ℤ).X ((p : ℤ) + q),
      a ≫ (L.step (p : ℤ)).arrow.f ((p : ℤ) + q) =
        ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
          J.ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) (by
            change q + (p : ℤ) = (p : ℤ) + q; omega) ∧
      IsIso (a ≫ (L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f
        ((p : ℤ) + q)) := by
    by_cases hq : 0 ≤ q
    · have H := Functor.graded_term_iso J L hL (p : ℤ) ((p : ℤ) + q) (by omega)
      have hn : (p : ℤ) + q - (p : ℤ) = q := by omega
      rw [hn] at H
      obtain ⟨b, hb, hbi⟩ := H
      let e : (J.X q).X (p : ℤ) ≅ R.X q :=
        (I.X q).extendXIso ComplexShape.embeddingUpNat (by rfl)
      refine ⟨e.inv ≫ b, ?_, ?_⟩
      · rw [Category.assoc, hb, J.ιTotalOrZero_eq (ComplexShape.up ℤ) q (p : ℤ)
          ((p : ℤ) + q) (by change q + (p : ℤ) = (p : ℤ) + q; omega)]
      · rw [Category.assoc]
        infer_instance
    · have hR : IsZero (R.X q) :=
        (HomologicalComplex.eval C (ComplexShape.up ℕ) p).map_isZero (hzero q (by omega))
      have hstep : L.complexStep (p : ℤ) ((p : ℤ) + q) = ⊥ := by
        rw [hL]
        simp [HomologicalComplex₂.secondFiltration,
          Finset.Icc_eq_empty_of_lt (by omega : (p : ℤ) + q < (p : ℤ))]
      have hG := Functor.gradedPiece_isZero_of_complexStep_eq_bot L (p : ℤ)
        ((p : ℤ) + q) hstep
      refine ⟨0, hR.eq_of_src _ _, hR.isIso hG _⟩
  choose a ha hai using hterms
  refine ⟨a, ha, hai, ?_⟩
  intro q
  by_cases hq : 0 ≤ q
  · let n := (p : ℤ) + q
    let n' := (p : ℤ) + (q + 1)
    let π := L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)
    let inc := Subobject.ofLE (L.step ((p : ℤ) + 1)) (L.step (p : ℤ))
      (L.antitone_step (by omega))
    let e : (J.X q).X (p : ℤ) ≅ R.X q :=
      (I.X q).extendXIso ComplexShape.embeddingUpNat (by rfl)
    let e' : (J.X (q + 1)).X (p : ℤ) ≅ R.X (q + 1) :=
      (I.X (q + 1)).extendXIso ComplexShape.embeddingUpNat (by rfl)
    obtain ⟨b, hb⟩ := Functor.inclusion_lift J L hL ((p : ℤ) + 1) q ((p : ℤ) + 1) n'
      (by dsimp [n']; omega)
      le_rfl (by dsimp [n']; omega)
    have hm : Mono ((L.step (p : ℤ)).arrow.f n') := by
      change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n').map
        (L.step (p : ℤ)).arrow)
      infer_instance
    have heq : a q ≫ (L.step (p : ℤ) : CochainComplex C ℤ).d n n' =
        R.d q (q + 1) ≫ a (q + 1) +
          (e.inv ≫ (q.negOnePow • (J.X q).d (p : ℤ) ((p : ℤ) + 1))) ≫
            b ≫ inc.f n' := by
      apply (cancel_mono ((L.step (p : ℤ)).arrow.f n')).1
      have hinc : inc.f n' ≫ (L.step (p : ℤ)).arrow.f n' =
          (L.step ((p : ℤ) + 1)).arrow.f n' :=
        congrArg (fun f ↦ f.f n')
          (Subobject.ofLE_arrow (L.antitone_step (show (p : ℤ) ≤ (p : ℤ) + 1 by omega)))
      simp only [Preadditive.add_comp, Category.assoc, hinc, hb]
      rw [← (L.step (p : ℤ)).arrow.comm, ← Category.assoc, ha q, Category.assoc,
        J.total_d, Preadditive.comp_add, Preadditive.comp_add, J.ι_D₁, J.ι_D₂]
      rw [J.d₁_eq' (ComplexShape.up ℤ) (show
          (ComplexShape.up ℤ).Rel q (q + 1) from rfl),
        J.d₂_eq' (ComplexShape.up ℤ) q (show
          (ComplexShape.up ℤ).Rel (p : ℤ) ((p : ℤ) + 1) from rfl)]
      change e.inv ≫ ((1 : ℤˣ) • _ ≫ _) + e.inv ≫ (q.negOnePow • _ ≫ _) = _
      rw [one_smul]
      have hD : (J.d q (q + 1)).f (p : ℤ) =
          e.hom ≫ R.d q (q + 1) ≫ e'.inv :=
        HomologicalComplex.extendMap_f (I.d q (q + 1)) ComplexShape.embeddingUpNat (by rfl)
      rw [hD]
      have ha' : a (q + 1) ≫ (L.step (p : ℤ)).arrow.f n' =
          e'.inv ≫ J.ιTotal (ComplexShape.up ℤ) (q + 1) (p : ℤ) n' (by
            change (q + 1) + (p : ℤ) = n'; dsimp [n']; omega) := ha (q + 1)
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [ha', J.ιTotalOrZero_eq (ComplexShape.up ℤ) (q + 1) (p : ℤ) n'
        (by change (q + 1) + (p : ℤ) = n'; dsimp [n']; omega),
        J.ιTotalOrZero_eq (ComplexShape.up ℤ) q ((p : ℤ) + 1) n'
          (by change q + ((p : ℤ) + 1) = n'; dsimp [n']; omega)]
      simp only [Linear.units_smul_comp]
    change (a q ≫ π.f n) ≫ (L.gradedPiece (p : ℤ)).d n n' =
      R.d q (q + 1) ≫ (a (q + 1) ≫ π.f n')
    change (a q ≫ π.f n) ≫ (L.complexQuotient (p : ℤ) ((p : ℤ) + 1) _).d n n' = _
    rw [Category.assoc, π.comm, ← Category.assoc, heq, Preadditive.add_comp]
    have hπ : inc.f n' ≫ π.f n' = 0 :=
      congrArg (fun f ↦ f.f n') (cokernel.condition inc)
    simp only [Category.assoc, hπ, comp_zero, add_zero]
  · exact ((HomologicalComplex.eval C (ComplexShape.up ℕ) p).map_isZero
      (hzero q (by omega))).eq_of_src _ _
private theorem column_map_image {X Y Z : C} (f : X ⟶ Y) (m : Y ⟶ Z) [Mono m] :
    (Subobject.map m).obj (imageSubobject f) = imageSubobject (f ≫ m) := by
  rw [← Subobject.exists_iso_map, Subobject.exists_obj_eq_imageSubobject,
    ← imageSubobject_comp_of_epi (factorThruImageSubobject f),
    ← Category.assoc, imageSubobject_arrow_comp]

private theorem column_first_page
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ k : ℤ, k < 0 → IsZero (I.X k))
    (L : DecreasingFiltration (HomologicalComplex₂.total
      (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      (HomologicalComplex₂.secondFiltration
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) n).step p)
    (p : ℕ) :
    let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
      ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    let R := I.flip.X p
    let K := J.total (ComplexShape.up ℤ)
    ∃ (e : ∀ q : ℤ, filteredComplexPageObject K L 1 ((p : ℤ), q) ≅ R.homology q)
      (t : ∀ q : ℤ, R.cycles q ⟶
        (L.step (p : ℤ) : CochainComplex C ℤ).X ((p : ℤ) + q))
      (x : ∀ q : ℤ, R.cycles q ⟶ (L.complexCycles (p : ℤ) ((p : ℤ) + q) 1 : C)),
      (∀ q, t q ≫ (L.step (p : ℤ)).arrow.f ((p : ℤ) + q) = R.iCycles q ≫
        ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
          J.ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) (by
            change q + (p : ℤ) = (p : ℤ) + q; omega)) ∧
      (∀ q, x q ≫ (L.complexCycles (p : ℤ) ((p : ℤ) + q) 1).arrow =
        t q ≫ (L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f ((p : ℤ) + q)) ∧
      (∀ q, x q ≫ filteredComplexPageπ K L 1 ((p : ℤ), q) ≫ (e q).hom =
        R.homologyπ q) := by
  classical
  dsimp only
  let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
  let R := I.flip.X p
  let K := J.total (ComplexShape.up ℤ)
  obtain ⟨a, ha, hai, hd⟩ := column_graded_terms I hzero L hL p
  let π : (L.step (p : ℤ) : CochainComplex C ℤ) ⟶ L.gradedPiece (p : ℤ) :=
    L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)
  have hcycles (q : ℤ) : ∃ c : R.cycles q ≅
      (L.complexCycles (p : ℤ) ((p : ℤ) + q) 1 : C),
      c.hom ≫ (L.complexCycles (p : ℤ) ((p : ℤ) + q) 1).arrow =
        R.iCycles q ≫ a q ≫ π.f ((p : ℤ) + q) := by
    let n := (p : ℤ) + q
    let n' := (p : ℤ) + (q + 1)
    have hZ := (L.filteredComplex_firstPage_cycles_boundaries (p : ℤ) n).1
    rw [show n + 1 = n' by dsimp [n, n']; omega] at hZ
    have hr : (ComplexShape.up ℤ).next q = q + 1 := by simp
    have := hai q
    have := hai (q + 1)
    let u : R.X q ≅ (L.gradedPiece (p : ℤ)).X n := asIso (a q ≫ π.f n)
    let v : R.X (q + 1) ≅ (L.gradedPiece (p : ℤ)).X n' :=
      asIso (a (q + 1) ≫ π.f n')
    let k := (R.cyclesIsKernel q (q + 1) hr).conePointUniqueUpToIso
      (kernelIsKernel (R.d q (q + 1)))
    let c := k ≪≫ Limits.kernel.mapIso (R.d q (q + 1))
      ((L.gradedPiece (p : ℤ)).d n n') u v (hd q).symm ≪≫
      (kernelSubobjectIso ((L.gradedPiece (p : ℤ)).d n n')).symm ≪≫
      Subobject.isoOfEq _ _ hZ.symm
    refine ⟨c, ?_⟩
    change c.hom ≫ (L.complexCycles (p : ℤ) n 1).arrow =
      R.iCycles q ≫ a q ≫ π.f n
    dsimp only [c, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow,
      kernelSubobject_arrow', Limits.kernel.mapIso_hom, Limits.kernel.map, Limits.kernel.lift_ι]
    rw [← Category.assoc]
    have hk : k.hom ≫ Limits.kernel.ι (R.d q (q + 1)) = R.iCycles q :=
      (R.cyclesIsKernel q (q + 1) hr).conePointUniqueUpToIso_hom_comp
        (kernelIsKernel (R.d q (q + 1))) WalkingParallelPair.zero
    rw [hk]
    rfl
  choose c hc using hcycles
  have hquot (q : ℤ) : Epi (filteredComplexPageπ K L 1 ((p : ℤ), q)) := by
    unfold filteredComplexPageπ
    infer_instance
  have hk (q : ℤ) :
      kernelSubobject ((c q).hom ≫ filteredComplexPageπ K L 1 ((p : ℤ), q)) =
        kernelSubobject (R.homologyπ q) := by
    let Z := L.complexCycles (p : ℤ) ((p : ℤ) + q) 1
    let B := L.complexBoundaries (p : ℤ) ((p : ℤ) + q) 1
    let inc := Subobject.ofLE B Z
      (filteredComplex_boundaries_le_cycles K L (p : ℤ) ((p : ℤ) + q) 1)
    let b := R.toCycles (q - 1) q
    have him : imageSubobject (b ≫ (c q).hom) = imageSubobject inc := by
      apply Subobject.map_obj_injective Z.arrow
      rw [column_map_image, column_map_image, Category.assoc, hc q,
        ← Category.assoc, HomologicalComplex.toCycles_i]
      rw [Subobject.ofLE_arrow, imageSubobject_mono B.arrow, Subobject.mk_arrow]
      dsimp only [B]
      rw [(L.filteredComplex_firstPage_cycles_boundaries (p : ℤ) ((p : ℤ) + q)).2]
      have H : (a (q - 1) ≫ π.f ((p : ℤ) + (q - 1))) ≫
          (L.gradedPiece (p : ℤ)).d ((p : ℤ) + (q - 1)) ((p : ℤ) + q) =
          R.d (q - 1) q ≫ a q ≫ π.f ((p : ℤ) + q) := by
        have H := hd (q - 1)
        change (a (q - 1) ≫ π.f ((p : ℤ) + (q - 1))) ≫
          (L.gradedPiece (p : ℤ)).d ((p : ℤ) + (q - 1)) ((p : ℤ) + (q - 1 + 1)) =
          R.d (q - 1) (q - 1 + 1) ≫ a (q - 1 + 1) ≫
            π.f ((p : ℤ) + (q - 1 + 1)) at H
        erw [Int.sub_add_cancel] at H
        exact H
      have hp : (p : ℤ) + (q - 1) = (p : ℤ) + q - 1 := by omega
      have := hai (q - 1)
      rw [← hp, ← H, imageSubobject_comp_of_epi]
    rw [← Functor.pullback_kernelSubobject]
    change (Subobject.pullback (c q).hom).obj (kernelSubobject (cokernel.π inc)) = _
    rw [Functor.kernelSubobject_of_cokernel inc _ (cokernel.condition inc) (cokernelIsCokernel inc),
      ← him, ← column_map_image, Subobject.pullback_map_self]
    exact (Functor.kernelSubobject_of_cokernel _ _
      (R.toCycles_comp_homologyπ (q - 1) q)
      (R.homologyIsCokernel (q - 1) q (by simp))).symm
  have hex (q : ℤ) : ∃ e : filteredComplexPageObject K L 1 ((p : ℤ), q) ≅ R.homology q,
      (c q).hom ≫ filteredComplexPageπ K L 1 ((p : ℤ), q) ≫ e.hom = R.homologyπ q := by
    have := hquot q
    obtain ⟨e, he⟩ := Functor.iso_of_kernelSubobject_eq
      ((c q).hom ≫ filteredComplexPageπ K L 1 ((p : ℤ), q)) (R.homologyπ q) (hk q)
    exact ⟨e, by simpa only [Category.assoc] using he⟩
  choose e he using hex
  refine ⟨e, fun q ↦ R.iCycles q ≫ a q, fun q ↦ (c q).hom, ?_, ?_, he⟩
  · intro q
    rw [Category.assoc, ha q]
  · intro q
    simpa only [Category.assoc] using hc q
private theorem column_cycle_total_d
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (p : ℕ) (q : ℤ) :
    let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
      ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    let R := I.flip.X p
    let R' := I.flip.X (p + 1)
    let f := I.flip.d p (p + 1)
    R.iCycles q ≫
        ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
        J.ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) (by
          change q + (p : ℤ) = (p : ℤ) + q; omega) ≫
        (J.total (ComplexShape.up ℤ)).d ((p : ℤ) + q) (((p + 1 : ℕ) : ℤ) + q) =
      q.negOnePow • (HomologicalComplex.cyclesMap f q ≫ R'.iCycles q ≫
        ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p + 1) (by rfl)).inv ≫
          J.ιTotal (ComplexShape.up ℤ) q ((p + 1 : ℕ) : ℤ)
            (((p + 1 : ℕ) : ℤ) + q) (by
              change q + ((p + 1 : ℕ) : ℤ) = ((p + 1 : ℕ) : ℤ) + q; omega)) := by
  let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
  let R := I.flip.X p
  let R' := I.flip.X (p + 1)
  let f := I.flip.d p (p + 1)
  let e (i : ℤ) (j : ℕ) : (J.X i).X (j : ℤ) ≅ (I.X i).X j :=
    (I.X i).extendXIso ComplexShape.embeddingUpNat (by rfl)
  change R.iCycles q ≫ (e q p).inv ≫
      J.ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) _ ≫
      (J.total (ComplexShape.up ℤ)).d ((p : ℤ) + q) (((p + 1 : ℕ) : ℤ) + q) =
    q.negOnePow • (HomologicalComplex.cyclesMap f q ≫ R'.iCycles q ≫
      (e q (p + 1)).inv ≫ J.ιTotal (ComplexShape.up ℤ) q ((p + 1 : ℕ) : ℤ)
        (((p + 1 : ℕ) : ℤ) + q) _)
  rw [J.total_d, Preadditive.comp_add, Preadditive.comp_add,
    Preadditive.comp_add]
  rw [J.ι_D₁, J.ι_D₂]
  rw [J.d₁_eq' (ComplexShape.up ℤ) (show
      (ComplexShape.up ℤ).Rel q (q + 1) from rfl),
    J.d₂_eq' (ComplexShape.up ℤ) q (show
      (ComplexShape.up ℤ).Rel (p : ℤ) ((p + 1 : ℕ) : ℤ) by simp)]
  have hD : (J.d q (q + 1)).f (p : ℤ) =
      (e q p).hom ≫ (I.d q (q + 1)).f p ≫ (e (q + 1) p).inv :=
    HomologicalComplex.extendMap_f (I.d q (q + 1)) ComplexShape.embeddingUpNat (by rfl)
  have hV : (J.X q).d (p : ℤ) ((p + 1 : ℕ) : ℤ) =
      (e q p).hom ≫ (I.X q).d p (p + 1) ≫ (e q (p + 1)).inv :=
    HomologicalComplex.extend_d_eq (I.X q) ComplexShape.embeddingUpNat (by rfl) (by rfl)
  rw [hD, hV]
  simp only [Linear.comp_units_smul, Category.assoc, Iso.inv_hom_id_assoc]
  change (1 : ℤˣ) • (R.iCycles q ≫ R.d q (q + 1) ≫ _) + q.negOnePow • _ = _
  rw [one_smul, HomologicalComplex.iCycles_d_assoc, zero_comp, zero_add,
    HomologicalComplex.cyclesMap_i_assoc]
  rw [J.ιTotalOrZero_eq (ComplexShape.up ℤ) q ((p + 1 : ℕ) : ℤ)
    (((p + 1 : ℕ) : ℤ) + q) (by
      change q + ((p + 1 : ℕ) : ℤ) = ((p + 1 : ℕ) : ℤ) + q; omega)]
  rfl
private theorem column_signed_first_page
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ k : ℤ, k < 0 → IsZero (I.X k))
    (L : DecreasingFiltration (HomologicalComplex₂.total
      (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      (HomologicalComplex₂.secondFiltration
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) n).step p)
    (D : FilteredComplexPageDifferential
      (HomologicalComplex₂.total
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) (ComplexShape.up ℤ)) L 1) :
    let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
      ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    let K := J.total (ComplexShape.up ℤ)
    ∃ (e : ∀ (p : ℕ) (q : ℤ), D.page.X ((p : ℤ), q) ≅ (I.flip.X p).homology q)
      (t : ∀ (p : ℕ) (q : ℤ), (I.flip.X p).cycles q ⟶
        (L.step (p : ℤ) : CochainComplex C ℤ).X ((p : ℤ) + q))
      (x : ∀ (p : ℕ) (q : ℤ), (I.flip.X p).cycles q ⟶
        (L.complexCycles (p : ℤ) ((p : ℤ) + q) 1 : C)),
      (∀ p q, t p q ≫ (L.step (p : ℤ)).arrow.f ((p : ℤ) + q) =
        (I.flip.X p).iCycles q ≫
          ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
            J.ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) (by
              change q + (p : ℤ) = (p : ℤ) + q; omega)) ∧
      (∀ p q, x p q ≫ (L.complexCycles (p : ℤ) ((p : ℤ) + q) 1).arrow =
        t p q ≫ (L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f
          ((p : ℤ) + q)) ∧
      (∀ p q, x p q ≫ filteredComplexPageπ K L 1 ((p : ℤ), q) ≫ (e p q).hom =
        (I.flip.X p).homologyπ q) ∧
      ∀ (p : ℕ) (q : ℤ),
        D.page.d ((p : ℤ), q) (((p + 1 : ℕ) : ℤ), q) ≫ (e (p + 1) q).hom =
          q.negOnePow • ((e p q).hom ≫
            HomologicalComplex.homologyMap (I.flip.d p (p + 1)) q) := by
  dsimp only
  classical
  let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
  let K := J.total (ComplexShape.up ℤ)
  have h (p : ℕ) := column_first_page I hzero L hL p
  choose e t x ht hx he using h
  refine ⟨e, t, x, ht, hx, he, ?_⟩
  intro p q
  let R := I.flip.X p
  let R' := I.flip.X (p + 1)
  let f := I.flip.d p (p + 1)
  let z := q.negOnePow
  let c := HomologicalComplex.cyclesMap f q
  let π := filteredComplexPageπ K L 1 ((p : ℤ), q)
  have hrep := D.on_representatives (R.cycles q) ((p : ℤ), q)
    (((p + 1 : ℕ) : ℤ), q) (by
      change ((p : ℤ), q) + (1, 1 - 1) = (((p + 1 : ℕ) : ℤ), q)
      ext <;> simp)
    (t p q) (z • (c ≫ t (p + 1) q))
    (x p q) (z • (c ≫ x (p + 1) q))
    (by
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [reassoc_of% (ht p q), ht (p + 1) q]
      exact column_cycle_total_d I p q)
    (hx p q)
    (by simp only [Linear.units_smul_comp, Category.assoc, hx (p + 1) q])
  have hπ : Epi (x p q ≫ π) := by
    apply (epi_comp_iff_of_isIso (x p q ≫ π) (e p q).hom).mp
    rw [Category.assoc, he p q]
    infer_instance
  apply (cancel_epi (x p q ≫ π)).1
  change (x p q ≫ π) ≫ D.d ((p : ℤ), q) (((p + 1 : ℕ) : ℤ), q) ≫
      (e (p + 1) q).hom =
    (x p q ≫ π) ≫ (z • ((e p q).hom ≫ HomologicalComplex.homologyMap f q))
  calc
    _ = (z • (c ≫ x (p + 1) q)) ≫
        filteredComplexPageπ K L 1 (((p + 1 : ℕ) : ℤ), q) ≫ (e (p + 1) q).hom := by
      simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ (e (p + 1) q).hom) hrep
    _ = z • (c ≫ R'.homologyπ q) := by
      simp only [Linear.units_smul_comp, Category.assoc]
      exact congrArg (fun g ↦ z • (c ≫ g)) (he (p + 1) q)
    _ = z • (R.homologyπ q ≫ HomologicalComplex.homologyMap f q) := by
      rw [HomologicalComplex.homologyπ_naturality]
    _ = _ := by
      simp only [Linear.comp_units_smul, ← Category.assoc]
      rw [Category.assoc (x p q) π, he p q]

private theorem column_eval_homology_d
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (q : ℤ) (p p' : ℕ) :
    HomologicalComplex.homologyMap (I.flip.d p p') q ≫
        ((I.sc q).mapHomologyIso (HomologicalComplex.eval C (ComplexShape.up ℕ) p')).hom =
      ((I.sc q).mapHomologyIso (HomologicalComplex.eval C (ComplexShape.up ℕ) p)).hom ≫
        (I.homology q).d p p' := by
  have H := NatTrans.app_homology
    (HomologicalComplex.dNatTrans C (ComplexShape.up ℕ) p p') (I.sc q)
  change (I.homology q).d p p' =
    ((I.sc q).mapHomologyIso (HomologicalComplex.eval C (ComplexShape.up ℕ) p)).inv ≫
      HomologicalComplex.homologyMap (I.flip.d p p') q ≫
        ((I.sc q).mapHomologyIso (HomologicalComplex.eval C (ComplexShape.up ℕ) p')).hom at H
  rw [H, Iso.hom_inv_id_assoc]

private theorem column_negative_page_zero
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration (HomologicalComplex₂.total
      (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      (HomologicalComplex₂.secondFiltration
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) n).step p)
    (p q : ℤ) (hp : p < 0) :
    IsZero (filteredComplexPageObject
      (HomologicalComplex₂.total
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) (ComplexShape.up ℤ)) L 1 (p, q)) := by
  let J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
  have hG : IsZero ((L.gradedPiece p).X (p + q)) := by
    by_cases hq : 0 ≤ q
    · obtain ⟨a, ha, hai⟩ := Functor.graded_term_iso J L hL p (p + q) (by omega)
      have hz : IsZero ((J.X (p + q - p)).X p) := by
        apply HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat
        intro n hn
        change (n : ℤ) = p at hn
        omega
      exact IsZero.of_iso hz (asIso (a ≫
        (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f (p + q))).symm
    · apply Functor.gradedPiece_isZero_of_complexStep_eq_bot
      rw [hL]
      simp [HomologicalComplex₂.secondFiltration,
        Finset.Icc_eq_empty_of_lt (by omega : p + q < p)]
  have hZ : IsZero (L.complexCycles p (p + q) 1 : C) :=
    IsZero.of_mono (L.complexCycles p (p + q) 1).arrow hG
  have : Epi (filteredComplexPageπ _ L 1 (p, q)) := by
    unfold filteredComplexPageπ
    infer_instance
  exact IsZero.of_epi (filteredComplexPageπ _ L 1 (p, q)) hZ

private theorem pair_first_page_prev (p q : ℤ) :
    (ComplexShape.up' ((1 : ℤ), (1 : ℤ) - 1)).prev (p, q) = (p - 1, q) := by
  apply ComplexShape.prev_eq'
  change (p - 1, q) + (1, 1 - 1) = (p, q)
  exact Prod.ext (by change p - 1 + 1 = p; omega)
    (by change q + (1 - 1) = q; omega)

private theorem nat_prev_no_rel (p : ℕ)
    (h : ¬ (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev p) p) : p = 0 := by
  cases p with
  | zero => rfl
  | succ i =>
    exfalso
    apply h
    rw [(ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel i (i + 1) from rfl)]
    rfl

private theorem column_page_prev_zero
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration (HomologicalComplex₂.total
      (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      (HomologicalComplex₂.secondFiltration
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) n).step p)
    (p : ℕ) (q : ℤ)
    (hp : ¬ (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev p) p) :
    IsZero (filteredComplexPageObject
      (HomologicalComplex₂.total
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) (ComplexShape.up ℤ)) L 1
      ((ComplexShape.up' ((1 : ℤ), (1 : ℤ) - 1)).prev ((p : ℤ), q))) := by
  rw [pair_first_page_prev, nat_prev_no_rel p hp]
  rw [show ((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) by decide]
  exact column_negative_page_zero I L hL (-1) q (by omega)

omit [IsGrothendieckAbelian.{v} C] in
private theorem natural_filtered_pages
    (K K' : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (F' : DecreasingFiltration K') (b : K ⟶ K')
    (s : ∀ p : ℤ, (F.step p : CochainComplex C ℤ) ⟶
      (F'.step p : CochainComplex C ℤ))
    (hs : ∀ p, s p ≫ (F'.step p).arrow = (F.step p).arrow ≫ b)
    (D : ∀ (r : ℤ) (_hr : 1 ≤ r), FilteredComplexPageDifferential K F r)
    (D' : ∀ (r : ℤ) (_hr : 1 ≤ r), FilteredComplexPageDifferential K' F' r) :
    ∃ (t : ∀ p n : ℤ, (F.gradedPiece p).X n ⟶ (F'.gradedPiece p).X n)
      (g : ∀ (r : ℤ) (_hr : 1 ≤ r) (pq : ℤ × ℤ),
        (F.complexCycles pq.1 (pq.1 + pq.2) r : C) ⟶
          (F'.complexCycles pq.1 (pq.1 + pq.2) r : C))
      (P : ∀ (r : ℤ) (hr : 1 ≤ r), (D r hr).page ⟶ (D' r hr).page),
      (∀ p n, (s p).f n ≫ (F'.complexQuotientπ p (p + 1) (by omega)).f n =
        (F.complexQuotientπ p (p + 1) (by omega)).f n ≫ t p n) ∧
      (∀ r hr pq, g r hr pq ≫ (F'.complexCycles pq.1 (pq.1 + pq.2) r).arrow =
        (F.complexCycles pq.1 (pq.1 + pq.2) r).arrow ≫ t pq.1 (pq.1 + pq.2)) ∧
      (∀ r hr pq, filteredComplexPageπ K F r pq ≫ (P r hr).f pq =
        g r hr pq ≫ filteredComplexPageπ K' F' r pq) := by
  classical
  obtain ⟨t, g, m, ht, hg, hm⟩ := filteredComplex_quotient_components K K' F F' b s hs
  have hsi (p n : ℤ) : (s p).f n ≫ (F'.step p).arrow.f n =
      (F.step p).arrow.f n ≫ b.f n := congrArg (fun f ↦ f.f n) (hs p)
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
        _ = (w ≫ g r hr j) ≫ filteredComplexPageπ K' F' r j := by
          simpa only [Category.assoc, reassoc_of% hm] using hleft
        _ = (w ≫ filteredComplexPageπ K F r j) ≫ m r hr j := by
          simp only [Category.assoc, hm]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun f ↦ f ≫ m r hr j) hright.symm
    · simp only [(D r hr).shape i j hij, (D' r hr).shape i j hij,
        comp_zero, zero_comp]
  exact ⟨t, g, fun r hr ↦ ⟨m r hr, fun i j _ ↦ hcomm r hr i j⟩, ht, hg, hm⟩

omit [IsGrothendieckAbelian.{v} C] in
private theorem normalized_page_two_natural
    (K K' : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (F' : DecreasingFiltration K')
    (D : FilteredComplexPageDifferential K F 1)
    (D' : FilteredComplexPageDifferential K' F' 1)
    (P : D.page ⟶ D'.page) (pq : ℤ × ℤ)
    (e : D.page.homology pq ≅ filteredComplexPageObject K F (1 + 1) pq)
    (e' : D'.page.homology pq ≅ filteredComplexPageObject K' F' (1 + 1) pq)
    (he : FilteredComplexHomologyNormalized K F 1 D pq e)
    (he' : FilteredComplexHomologyNormalized K' F' 1 D' pq e')
    (t : (F.gradedPiece pq.1).X (pq.1 + pq.2) ⟶
      (F'.gradedPiece pq.1).X (pq.1 + pq.2))
    (g₁ : (F.complexCycles pq.1 (pq.1 + pq.2) 1 : C) ⟶
      (F'.complexCycles pq.1 (pq.1 + pq.2) 1 : C))
    (g₂ : (F.complexCycles pq.1 (pq.1 + pq.2) (1 + 1) : C) ⟶
      (F'.complexCycles pq.1 (pq.1 + pq.2) (1 + 1) : C))
    (m₂ : filteredComplexPageObject K F (1 + 1) pq ⟶ filteredComplexPageObject K' F' (1 + 1) pq)
    (hg₁ : g₁ ≫ (F'.complexCycles pq.1 (pq.1 + pq.2) 1).arrow =
      (F.complexCycles pq.1 (pq.1 + pq.2) 1).arrow ≫ t)
    (hg₂ : g₂ ≫ (F'.complexCycles pq.1 (pq.1 + pq.2) (1 + 1)).arrow =
      (F.complexCycles pq.1 (pq.1 + pq.2) (1 + 1)).arrow ≫ t)
    (hm₁ : filteredComplexPageπ K F 1 pq ≫ P.f pq =
      g₁ ≫ filteredComplexPageπ K' F' 1 pq)
    (hm₂ : filteredComplexPageπ K F (1 + 1) pq ≫ m₂ =
      g₂ ≫ filteredComplexPageπ K' F' (1 + 1) pq) :
    HomologicalComplex.homologyMap P pq ≫ e'.hom = e.hom ≫ m₂ := by
  let hZ := filteredComplex_cycles_successor_le K F 1 pq
  let hZ' := filteredComplex_cycles_successor_le K' F' 1 pq
  obtain ⟨f, hfepi, hf⟩ := filteredComplex_successor_cycles_cover K F 1 (by omega) D pq hZ
  obtain ⟨f', _, hf'⟩ := filteredComplex_successor_cycles_cover K' F' 1 (by omega) D' pq hZ'
  have : Epi f := hfepi
  let j := Subobject.ofLE _ _ hZ
  let j' := Subobject.ofLE _ _ hZ'
  have hj : g₂ ≫ j' = j ≫ g₁ := by
    apply (cancel_mono (F'.complexCycles pq.1 (pq.1 + pq.2) 1).arrow).1
    dsimp only [j, j']
    rw [Category.assoc, Subobject.ofLE_arrow, hg₂, Category.assoc, hg₁,
      ← Category.assoc, Subobject.ofLE_arrow]
  have hc : g₂ ≫ f' = f ≫ HomologicalComplex.cyclesMap P pq := by
    apply (cancel_mono (D'.page.iCycles pq)).1
    calc
      _ = g₂ ≫ j' ≫ filteredComplexPageπ K' F' 1 pq := by
        rw [Category.assoc, hf']
      _ = j ≫ g₁ ≫ filteredComplexPageπ K' F' 1 pq := by
        rw [← Category.assoc, hj, Category.assoc]
      _ = j ≫ filteredComplexPageπ K F 1 pq ≫ P.f pq := by rw [hm₁]
      _ = _ := by
        simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
        simpa only [Category.assoc] using (congrArg (fun a ↦ a ≫ P.f pq) hf).symm
  have he₀ := he hZ f hf
  have he₀' := he' hZ' f' hf'
  apply (cancel_epi (f ≫ D.page.homologyπ pq)).1
  calc
    _ = f ≫ HomologicalComplex.cyclesMap P pq ≫ D'.page.homologyπ pq ≫ e'.hom := by
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
    _ = g₂ ≫ filteredComplexPageπ K' F' (1 + 1) pq := by
      rw [← Category.assoc f, ← hc]
      simp only [Category.assoc, he₀']
    _ = filteredComplexPageπ K F (1 + 1) pq ≫ m₂ := hm₂.symm
    _ = _ := by
      simpa only [Category.assoc] using
        (congrArg (fun a ↦ a ≫ m₂) he₀).symm

omit [IsGrothendieckAbelian.{v} C] in
private theorem normalized_first_page_natural
    (K K' R R' : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (F' : DecreasingFiltration K')
    (p q : ℤ) (b : K ⟶ K') (f : R ⟶ R')
    (s : (F.step p : CochainComplex C ℤ) ⟶ (F'.step p : CochainComplex C ℤ))
    (hs : s ≫ (F'.step p).arrow = (F.step p).arrow ≫ b)
    (i : R.X q ⟶ K.X (p + q)) (i' : R'.X q ⟶ K'.X (p + q))
    (hi : i ≫ b.f (p + q) = f.f q ≫ i')
    (v : (F.gradedPiece p).X (p + q) ⟶ (F'.gradedPiece p).X (p + q))
    (hv : s.f (p + q) ≫ (F'.complexQuotientπ p (p + 1) (by omega)).f (p + q) =
      (F.complexQuotientπ p (p + 1) (by omega)).f (p + q) ≫ v)
    (g : (F.complexCycles p (p + q) 1 : C) ⟶ (F'.complexCycles p (p + q) 1 : C))
    (hg : g ≫ (F'.complexCycles p (p + q) 1).arrow =
      (F.complexCycles p (p + q) 1).arrow ≫ v)
    (m : filteredComplexPageObject K F 1 (p, q) ⟶ filteredComplexPageObject K' F' 1 (p, q))
    (hm : filteredComplexPageπ K F 1 (p, q) ≫ m =
      g ≫ filteredComplexPageπ K' F' 1 (p, q))
    (t : R.cycles q ⟶ (F.step p : CochainComplex C ℤ).X (p + q))
    (t' : R'.cycles q ⟶ (F'.step p : CochainComplex C ℤ).X (p + q))
    (ht : t ≫ (F.step p).arrow.f (p + q) = R.iCycles q ≫ i)
    (ht' : t' ≫ (F'.step p).arrow.f (p + q) = R'.iCycles q ≫ i')
    (x : R.cycles q ⟶ (F.complexCycles p (p + q) 1 : C))
    (x' : R'.cycles q ⟶ (F'.complexCycles p (p + q) 1 : C))
    (hx : x ≫ (F.complexCycles p (p + q) 1).arrow =
      t ≫ (F.complexQuotientπ p (p + 1) (by omega)).f (p + q))
    (hx' : x' ≫ (F'.complexCycles p (p + q) 1).arrow =
      t' ≫ (F'.complexQuotientπ p (p + 1) (by omega)).f (p + q))
    (e : filteredComplexPageObject K F 1 (p, q) ≅ R.homology q)
    (e' : filteredComplexPageObject K' F' 1 (p, q) ≅ R'.homology q)
    (he : x ≫ filteredComplexPageπ K F 1 (p, q) ≫ e.hom = R.homologyπ q)
    (he' : x' ≫ filteredComplexPageπ K' F' 1 (p, q) ≫ e'.hom = R'.homologyπ q) :
    m ≫ e'.hom = e.hom ≫ HomologicalComplex.homologyMap f q := by
  have hsi := congrArg (fun h ↦ h.f (p + q)) hs
  simp only [HomologicalComplex.comp_f] at hsi
  have htn : t ≫ s.f (p + q) = HomologicalComplex.cyclesMap f q ≫ t' := by
    apply (cancel_mono ((F'.step p).arrow.f (p + q))).1
    simp only [Category.assoc, hsi, reassoc_of% ht, hi, ht',
      HomologicalComplex.cyclesMap_i_assoc]
  have hxn : x ≫ g = HomologicalComplex.cyclesMap f q ≫ x' := by
    apply (cancel_mono (F'.complexCycles p (p + q) 1).arrow).1
    rw [Category.assoc, hg, ← Category.assoc, hx, Category.assoc, ← hv,
      ← Category.assoc, htn]
    simp only [Category.assoc, hx']
  have : Epi (x ≫ filteredComplexPageπ K F 1 (p, q)) := by
    apply (epi_comp_iff_of_isIso _ e.hom).mp
    rw [Category.assoc, he]
    infer_instance
  apply (cancel_epi (x ≫ filteredComplexPageπ K F 1 (p, q))).1
  calc
    _ = x ≫ g ≫ filteredComplexPageπ K' F' 1 (p, q) ≫ e'.hom := by
      simp only [Category.assoc, reassoc_of% hm]
    _ = HomologicalComplex.cyclesMap f q ≫ R'.homologyπ q := by
      rw [← Category.assoc x g, hxn]
      simpa only [Category.assoc] using
        congrArg (fun a ↦ HomologicalComplex.cyclesMap f q ≫ a) he'
    _ = R.homologyπ q ≫ HomologicalComplex.homologyMap f q :=
      (HomologicalComplex.homologyπ_naturality f q).symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun a ↦ a ≫ HomologicalComplex.homologyMap f q) he.symm

omit [IsGrothendieckAbelian.{v} C] in
private theorem normalized_two_column_image
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ)
    (φ : F.complexQuotient p (p + 2) (by omega) ⟶
      F.complexQuotient (p - 2 + 1) (p + 1) (by omega))
    (hφ : F.complexQuotientπ p (p + 2) (by omega) ≫ φ =
      Subobject.ofLE (F.step p) (F.step (p - 2 + 1)) (F.antitone_step (by omega)) ≫
        F.complexQuotientπ (p - 2 + 1) (p + 1) (by omega)) :
    let R := F.complexCycleRepresentatives p (p + q) 2
    let S := F.complexQuotient p (p + 2) (by omega)
    ∃ (z : (R : C) ⟶ (F.complexCycles p (p + q) 2 : C))
      (g : (R : C) ⟶ S.cycles (p + q))
      (e : filteredComplexPageObject K F 2 (p, q) ≅
        image (HomologicalComplex.homologyMap φ (p + q))),
      Epi z ∧
      z ≫ (F.complexCycles p (p + q) 2).arrow = R.arrow ≫
        (F.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
      g ≫ S.iCycles (p + q) = R.arrow ≫
        (F.complexQuotientπ p (p + 2) (by omega)).f (p + q) ∧
      z ≫ filteredComplexPageπ K F 2 (p, q) ≫ e.hom ≫
          image.ι (HomologicalComplex.homologyMap φ (p + q)) =
        g ≫ S.homologyπ (p + q) ≫ HomologicalComplex.homologyMap φ (p + q) := by
  have hBZ := filteredComplex_boundaries_le_cycles K F p (p + q) 2
  obtain ⟨ha, hb, ψ, hψ, z, g, hz, hg, e, he⟩ :=
    F.filteredComplex_quotient_image_comparison p (p + q) 2 (by omega) hBZ
  have hψφ : ψ = φ := by
    have : Epi (F.complexQuotientπ p (p + 2) (by omega)) := by
      unfold DecreasingFiltration.complexQuotientπ
      infer_instance
    apply (cancel_epi (F.complexQuotientπ p (p + 2)
      (show p ≤ p + 2 from le_add_of_nonneg_right (by decide)))).1
    exact hψ.trans hφ.symm
  subst ψ
  obtain ⟨z', g', hzepi, _, hz', _⟩ :=
    F.filteredComplex_representative_epis p (p + q) 2 (by omega)
  have hzz : z = z' := by
    apply (cancel_mono (F.complexCycles p (p + q) 2).arrow).1
    exact hz.trans hz'.symm
  have : Epi z := by rw [hzz]; exact hzepi
  exact ⟨z, g, e, inferInstance, hz, hg, he⟩

private noncomputable abbrev columnExtension
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I

private noncomputable abbrev columnTotal
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)) : CochainComplex C ℤ :=
  (columnExtension I).total (ComplexShape.up ℤ)

private structure ColumnPageData
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration (columnTotal I))
    (D : FilteredComplexPageDifferential (columnTotal I) L 1) where
  e : ∀ (p : ℕ) (q : ℤ), D.page.X ((p : ℤ), q) ≅ (I.flip.X p).homology q
  t : ∀ (p : ℕ) (q : ℤ), (I.flip.X p).cycles q ⟶
    (L.step (p : ℤ) : CochainComplex C ℤ).X ((p : ℤ) + q)
  x : ∀ (p : ℕ) (q : ℤ), (I.flip.X p).cycles q ⟶
    (L.complexCycles (p : ℤ) ((p : ℤ) + q) 1 : C)
  ht : ∀ (p : ℕ) (q : ℤ), t p q ≫ (L.step (p : ℤ)).arrow.f ((p : ℤ) + q) =
    (I.flip.X p).iCycles q ≫
      ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
        (columnExtension I).ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) (by
          change q + (p : ℤ) = (p : ℤ) + q; omega)
  hx : ∀ (p : ℕ) (q : ℤ), x p q ≫ (L.complexCycles (p : ℤ) ((p : ℤ) + q) 1).arrow =
    t p q ≫ (L.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f ((p : ℤ) + q)
  he : ∀ (p : ℕ) (q : ℤ), x p q ≫ filteredComplexPageπ (columnTotal I) L 1 ((p : ℤ), q) ≫
    (e p q).hom = (I.flip.X p).homologyπ q
  hd : ∀ (p : ℕ) (q : ℤ), D.page.d ((p : ℤ), q) (((p + 1 : ℕ) : ℤ), q) ≫ (e (p + 1) q).hom =
    q.negOnePow • ((e p q).hom ≫ HomologicalComplex.homologyMap (I.flip.d p (p + 1)) q)

private noncomputable def makeColumnPageData
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ k : ℤ, k < 0 → IsZero (I.X k))
    (L : DecreasingFiltration (columnTotal I))
    (hL : ∀ p n : ℤ, L.complexStep p n = ((columnExtension I).secondFiltration n).step p)
    (D : FilteredComplexPageDifferential (columnTotal I) L 1) : ColumnPageData I L D :=
  Classical.choice (by
    obtain ⟨e, t, x, ht, hx, he, hd⟩ := column_signed_first_page I hzero L hL D
    exact ⟨⟨e, t, x, ht, hx, he, hd⟩⟩)

private noncomputable def ColumnPageData.unsigned
    {I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    {L : DecreasingFiltration (columnTotal I)}
    {D : FilteredComplexPageDifferential (columnTotal I) L 1}
    (A : ColumnPageData I L D) (p : ℕ) (q : ℤ) :
    D.page.X ((p : ℤ), q) ≅ (I.homology q).X p :=
  ((q * (p : ℤ)).negOnePow • A.e p q) ≪≫
    ((I.sc q).mapHomologyIso (HomologicalComplex.eval C (ComplexShape.up ℕ) p))

private theorem ColumnPageData.unsigned_d
    {I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    {L : DecreasingFiltration (columnTotal I)}
    {D : FilteredComplexPageDifferential (columnTotal I) L 1}
    (A : ColumnPageData I L D) (p : ℕ) (q : ℤ) :
    D.page.d ((p : ℤ), q) (((p + 1 : ℕ) : ℤ), q) ≫ (A.unsigned (p + 1) q).hom =
      (A.unsigned p q).hom ≫ (I.homology q).d p (p + 1) := by
  dsimp only [ColumnPageData.unsigned, Iso.trans_hom, Preadditive.smul_iso_hom]
  rw [← Category.assoc, Linear.comp_units_smul, A.hd]
  simp only [Linear.units_smul_comp, smul_smul]
  rw [show q * ((p + 1 : ℕ) : ℤ) = q * (p : ℤ) + q by simp [mul_add],
    Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
  rw [Category.assoc, column_eval_homology_d]
  simp only [Category.assoc]

private noncomputable def ColumnPageData.homologyIso
    {I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    {L : DecreasingFiltration (columnTotal I)}
    {D : FilteredComplexPageDifferential (columnTotal I) L 1}
    (A : ColumnPageData I L D)
    (hL : ∀ p n : ℤ, L.complexStep p n = ((columnExtension I).secondFiltration n).step p)
    (p : ℕ) (q : ℤ) : D.page.homology ((p : ℤ), q) ≅ (I.homology q).homology p :=
  (HomologicalComplex.homologyIsoOfComponents D.page (I.homology q)
    (fun i : ℕ ↦ ((i : ℤ), q)) (fun i ↦ (A.unsigned i q).symm)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      change (I.homology q).d i (i + 1) ≫ (A.unsigned (i + 1) q).inv =
        (A.unsigned i q).inv ≫ D.page.d ((i : ℤ), q) (((i + 1 : ℕ) : ℤ), q)
      rw [Iso.eq_inv_comp, ← Category.assoc, ← A.unsigned_d, Category.assoc,
        Iso.hom_inv_id, Category.comp_id])
    (by
      intro i j hij
      change i + 1 = j at hij
      change ((i : ℤ), q) + (1, 1 - 1) = ((j : ℤ), q)
      exact Prod.ext (by change (i : ℤ) + 1 = (j : ℤ); omega)
        (by change q + (1 - 1) = q; omega))
    p (column_page_prev_zero I L hL p q)
    (by intro h; apply (h _).elim; simp)).symm

private structure TwoColumnImageData
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ)
    (φ : F.complexQuotient p (p + 2) (by omega) ⟶
      F.complexQuotient (p - 2 + 1) (p + 1) (by omega)) where
  z : (F.complexCycleRepresentatives p (p + q) 2 : C) ⟶
    (F.complexCycles p (p + q) 2 : C)
  g : (F.complexCycleRepresentatives p (p + q) 2 : C) ⟶
    (F.complexQuotient p (p + 2) (by omega)).cycles (p + q)
  e : filteredComplexPageObject K F 2 (p, q) ≅
    image (HomologicalComplex.homologyMap φ (p + q))
  epi : Epi z
  hz : z ≫ (F.complexCycles p (p + q) 2).arrow =
    (F.complexCycleRepresentatives p (p + q) 2).arrow ≫
      (F.complexQuotientπ p (p + 1) (by omega)).f (p + q)
  hg : g ≫ (F.complexQuotient p (p + 2) (by omega)).iCycles (p + q) =
    (F.complexCycleRepresentatives p (p + q) 2).arrow ≫
      (F.complexQuotientπ p (p + 2) (by omega)).f (p + q)
  he : z ≫ filteredComplexPageπ K F 2 (p, q) ≫ e.hom ≫
      image.ι (HomologicalComplex.homologyMap φ (p + q)) =
    g ≫ (F.complexQuotient p (p + 2) (by omega)).homologyπ (p + q) ≫
      HomologicalComplex.homologyMap φ (p + q)

private noncomputable def makeTwoColumnImageData
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ)
    (φ : F.complexQuotient p (p + 2) (by omega) ⟶
      F.complexQuotient (p - 2 + 1) (p + 1) (by omega))
    (hφ : F.complexQuotientπ p (p + 2) (by omega) ≫ φ =
      Subobject.ofLE (F.step p) (F.step (p - 2 + 1)) (F.antitone_step (by omega)) ≫
        F.complexQuotientπ (p - 2 + 1) (p + 1) (by omega)) :
    TwoColumnImageData K F p q φ := Classical.choice (by
  obtain ⟨z, g, e, epi, hz, hg, he⟩ := normalized_two_column_image K F p q φ hφ
  exact ⟨⟨z, g, e, epi, hz, hg, he⟩⟩)

private theorem ColumnPageData.homologyIso_natural
    {I I' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    {L : DecreasingFiltration (columnTotal I)} {L' : DecreasingFiltration (columnTotal I')}
    {D : FilteredComplexPageDifferential (columnTotal I) L 1}
    {D' : FilteredComplexPageDifferential (columnTotal I') L' 1}
    (A : ColumnPageData I L D) (B : ColumnPageData I' L' D')
    (hL : ∀ p n : ℤ, L.complexStep p n = ((columnExtension I).secondFiltration n).step p)
    (hL' : ∀ p n : ℤ, L'.complexStep p n = ((columnExtension I').secondFiltration n).step p)
    (P : D.page ⟶ D'.page) (f : I ⟶ I') (p : ℕ) (q : ℤ)
    (he : ∀ i : ℕ, P.f ((i : ℤ), q) ≫ (B.unsigned i q).hom =
      (A.unsigned i q).hom ≫ (HomologicalComplex.homologyMap f q).f i) :
    HomologicalComplex.homologyMap P ((p : ℤ), q) ≫ (B.homologyIso hL' p q).hom =
      (A.homologyIso hL p q).hom ≫
        HomologicalComplex.homologyMap (HomologicalComplex.homologyMap f q) p := by
  dsimp only [ColumnPageData.homologyIso, Iso.symm_hom,
    HomologicalComplex.homologyIsoOfComponents, ShortComplex.homologyIsoOfτ₂,
    HomologicalComplex.homologyMap]
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  apply ShortComplex.homologyMap_congr_τ₂
  exact he p

private theorem TwoColumnImageData.natural
    {K K' : CochainComplex C ℤ} {F : DecreasingFiltration K}
    {F' : DecreasingFiltration K'} {p q : ℤ}
    {φ : F.complexQuotient p (p + 2) (by omega) ⟶
      F.complexQuotient (p - 2 + 1) (p + 1) (by omega)}
    {φ' : F'.complexQuotient p (p + 2) (by omega) ⟶
      F'.complexQuotient (p - 2 + 1) (p + 1) (by omega)}
    (A : TwoColumnImageData K F p q φ) (B : TwoColumnImageData K' F' p q φ')
    (hφ : F.complexQuotientπ p (p + 2) (by omega) ≫ φ =
      Subobject.ofLE (F.step p) (F.step (p - 2 + 1)) (F.antitone_step (by omega)) ≫
        F.complexQuotientπ (p - 2 + 1) (p + 1) (by omega))
    (hφ' : F'.complexQuotientπ p (p + 2) (by omega) ≫ φ' =
      Subobject.ofLE (F'.step p) (F'.step (p - 2 + 1)) (F'.antitone_step (by omega)) ≫
        F'.complexQuotientπ (p - 2 + 1) (p + 1) (by omega))
    (b : K ⟶ K')
    (s : ∀ i : ℤ, (F.step i : CochainComplex C ℤ) ⟶ (F'.step i : CochainComplex C ℤ))
    (hs : ∀ i, s i ≫ (F'.step i).arrow = (F.step i).arrow ≫ b)
    (β : F.complexQuotient (p - 2 + 1) (p + 1) (by omega) ⟶
      F'.complexQuotient (p - 2 + 1) (p + 1) (by omega))
    (hβ : F.complexQuotientπ (p - 2 + 1) (p + 1) (by omega) ≫ β =
      s (p - 2 + 1) ≫ F'.complexQuotientπ (p - 2 + 1) (p + 1) (by omega))
    (v : (F.gradedPiece p).X (p + q) ⟶ (F'.gradedPiece p).X (p + q))
    (hv : (s p).f (p + q) ≫ (F'.complexQuotientπ p (p + 1) (by omega)).f (p + q) =
      (F.complexQuotientπ p (p + 1) (by omega)).f (p + q) ≫ v)
    (kz : (F.complexCycles p (p + q) 2 : C) ⟶ (F'.complexCycles p (p + q) 2 : C))
    (hkz : kz ≫ (F'.complexCycles p (p + q) 2).arrow =
      (F.complexCycles p (p + q) 2).arrow ≫ v)
    (m : filteredComplexPageObject K F 2 (p, q) ⟶ filteredComplexPageObject K' F' 2 (p, q))
    (hm : filteredComplexPageπ K F 2 (p, q) ≫ m =
      kz ≫ filteredComplexPageπ K' F' 2 (p, q)) :
    m ≫ B.e.hom ≫ image.ι (HomologicalComplex.homologyMap φ' (p + q)) =
      A.e.hom ≫ image.ι (HomologicalComplex.homologyMap φ (p + q)) ≫
        HomologicalComplex.homologyMap β (p + q) := by
  have : Epi A.z := A.epi
  have : Epi (filteredComplexPageπ K F 2 (p, q)) := by
    unfold filteredComplexPageπ
    infer_instance
  obtain ⟨a, ha⟩ := quotient_descent F F' b s hs p (p + 2) (by omega)
  have hw : a ≫ φ' = φ ≫ β := by
    have : Epi (F.complexQuotientπ p (p + 2) (by omega)) := by
      unfold DecreasingFiltration.complexQuotientπ
      infer_instance
    apply (cancel_epi (F.complexQuotientπ p (p + 2)
      (show p ≤ p + 2 from le_add_of_nonneg_right (by decide)))).1
    rw [← Category.assoc, ha, Category.assoc, hφ', ← Category.assoc,
      ← step_restriction_square F F' b s hs (p - 2 + 1) p (by omega),
      Category.assoc, ← hβ, ← Category.assoc, ← hφ, Category.assoc]
  have hstep := preserves_steps K K' F F' b s hs
  have hrep : F.complexCycleRepresentatives p (p + q) 2 ≤
      (Subobject.pullback ((s p).f (p + q))).obj
        (F'.complexCycleRepresentatives p (p + q) 2) := by
    unfold DecreasingFiltration.complexCycleRepresentatives
    apply preserves_pullback _ _ _ _ (congrArg (fun h ↦ h.f (p + q)) (hs p)).symm
    apply preserves_inf
    · exact hstep p (p + q)
    · exact preserves_pullback (b.f (p + q)) (b.f (p + q + 1))
        (K.d (p + q) (p + q + 1)) (K'.d (p + q) (p + q + 1))
        (b.comm _ _).symm _ _ (hstep (p + 2) (p + q + 1))
  obtain ⟨ρ, hρ⟩ := restriction _ _ _ hrep
  have hzρ : A.z ≫ kz = ρ ≫ B.z := by
    apply (cancel_mono (F'.complexCycles p (p + q) 2).arrow).1
    rw [Category.assoc, hkz, ← Category.assoc, A.hz, Category.assoc, ← hv,
      ← Category.assoc, ← hρ, Category.assoc, ← B.hz, ← Category.assoc]
  have hgρ : A.g ≫ HomologicalComplex.cyclesMap a (p + q) = ρ ≫ B.g := by
    apply (cancel_mono ((F'.complexQuotient p (p + 2) (by omega)).iCycles (p + q))).1
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
    rw [← Category.assoc, A.hg]
    have ha' := congrArg (fun h ↦ h.f (p + q)) ha
    simp only [HomologicalComplex.comp_f] at ha'
    rw [Category.assoc, ha', ← Category.assoc, ← hρ, Category.assoc, ← B.hg]
  exact normalized_image_naturality (p + q) a β φ φ' hw ρ A.z B.z A.g B.g
    (filteredComplexPageπ K F 2 (p, q)) (filteredComplexPageπ K' F' 2 (p, q))
    A.e.hom B.e.hom A.he B.he kz m hzρ hgρ hm
private theorem filtered_map_of_degreewise
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : CochainComplex C ℤ} (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (a : K ⟶ L)
    (ha : ∀ p n : ℤ,
      (G.complexStep p n).Factors ((F.step p).arrow.f n ≫ a.f n)) :
    ∃ t : (⟨K, F⟩ : FilteredObject (CochainComplex C ℤ)) ⟶ ⟨L, G⟩, t.hom = a := by
  classical
  refine ⟨⟨a, ?_⟩, rfl⟩
  intro p
  have hf (n : ℤ) : (Subobject.mk ((G.step p).arrow.f n)).Factors
      ((F.step p).arrow.f n ≫ a.f n) := by
    simpa only [DecreasingFiltration.complexStep, imageSubobject_mono] using ha p n
  let f (n : ℤ) := (Subobject.mk ((G.step p).arrow.f n)).factorThru _ (hf n) ≫
    (Subobject.underlyingIso ((G.step p).arrow.f n)).hom
  have hfac (n : ℤ) : f n ≫ (G.step p).arrow.f n =
      (F.step p).arrow.f n ≫ a.f n := by
    simp [f, Category.assoc]
  refine ⟨{ f := f, comm' := ?_ }, ?_⟩
  · intro i j hij
    apply (cancel_mono ((G.step p).arrow.f j)).1
    simp only [Category.assoc, ← (G.step p).arrow.comm, reassoc_of% hfac, a.comm]
    rw [hfac, ← Category.assoc, (F.step p).arrow.comm, Category.assoc]
  · ext n
    exact hfac n

private theorem total_secondFiltration_map
    {C : Type u} [Category.{v} C] [Abelian C]
    (K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (F : DecreasingFiltration (K.total (ComplexShape.up ℤ)))
    (G : DecreasingFiltration (L.total (ComplexShape.up ℤ)))
    (hF : ∀ p n : ℤ, F.complexStep p n = (K.secondFiltration n).step p)
    (hG : ∀ p n : ℤ, G.complexStep p n = (L.secondFiltration n).step p)
    (a : K ⟶ L) :
    ∃ t : (⟨K.total (ComplexShape.up ℤ), F⟩ :
        FilteredObject (CochainComplex C ℤ)) ⟶ ⟨L.total (ComplexShape.up ℤ), G⟩,
      t.hom = HomologicalComplex₂.total.map a (ComplexShape.up ℤ) := by
  apply filtered_map_of_degreewise
  intro p n
  let d := (HomologicalComplex₂.total.map a (ComplexShape.up ℤ)).f n
  let Q := G.complexStep p n
  let P := (Subobject.pullback d).obj Q
  have hs : F.complexStep p n ≤ P := by
    rw [hF]
    change (Finset.Icc p n).sup _ ≤ P
    apply Finset.sup_le
    intro i hi
    have hgen : Q.Factors
        (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n ≫ d) := by
      rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - i) i n (by
        change (n - i) + i = n; omega)]
      dsimp only [d]
      rw [HomologicalComplex₂.ιTotal_map]
      apply Subobject.factors_of_factors_right
      have hle : imageSubobject (L.ιTotal (ComplexShape.up ℤ) (n - i) i n (by
          change (n - i) + i = n; omega)) ≤ Q := by
        dsimp only [Q]
        rw [hG]
        have h := Finset.le_sup (f := fun j ↦ imageSubobject
          (L.ιTotalOrZero (ComplexShape.up ℤ) (n - j) j n)) hi
        simpa only [DecreasingFiltration.step, HomologicalComplex₂.secondFiltration,
          L.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - i) i n (by
          change (n - i) + i = n; omega)] using h
      apply Subobject.factors_of_le _ hle
      simpa using imageSubobject_factors_comp_self
        (L.ιTotal (ComplexShape.up ℤ) (n - i) i n (by
          change (n - i) + i = n; omega)) (𝟙 _)
    have hp := pullback_factors d Q
      (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n) hgen
    exact imageSubobject_le _ (P.factorThru _ hp) (Subobject.factorThru_arrow _ _ _)
  apply (pullback_factors_iff d Q _).1
  change P.Factors ((F.step p).arrow.f n)
  apply Subobject.factors_of_le _ hs
  simpa only [DecreasingFiltration.complexStep, Category.id_comp] using
    imageSubobject_factors_comp_self ((F.step p).arrow.f n) (𝟙 _)


private theorem column_total_inclusion_natural
    {I I' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    (f : I ⟶ I') (p : ℕ) (q : ℤ) :
    ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
        (columnExtension I).ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) (by
          change q + (p : ℤ) = (p : ℤ) + q; omega) ≫
        (HomologicalComplex₂.total.map
          (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f) (ComplexShape.up ℤ)).f ((p : ℤ) + q) =
      (f.f q).f p ≫
        ((I'.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
          (columnExtension I').ιTotal (ComplexShape.up ℤ) q (p : ℤ) ((p : ℤ) + q) (by
            change q + (p : ℤ) = (p : ℤ) + q; omega) := by
  rw [HomologicalComplex₂.ιTotal_map]
  change ((I.X q).extendXIso ComplexShape.embeddingUpNat (i := p) (by rfl)).inv ≫
      (HomologicalComplex.extendMap (f.f q) ComplexShape.embeddingUpNat).f (p : ℤ) ≫ _ = _
  rw [HomologicalComplex.extendMap_f (f.f q) ComplexShape.embeddingUpNat (by rfl)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem column_eval_homology_map
    {I I' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    (f : I ⟶ I') (p : ℕ) (q : ℤ) :
    HomologicalComplex.homologyMap
        (((HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℕ)).map f).f p)
        q ≫ ((I'.sc q).mapHomologyIso
          (HomologicalComplex.eval C (ComplexShape.up ℕ) p)).hom =
      ((I.sc q).mapHomologyIso (HomologicalComplex.eval C (ComplexShape.up ℕ) p)).hom ≫
        (HomologicalComplex.homologyMap f q).f p := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor
      (CochainComplex C ℕ) (ComplexShape.up ℤ) q).map f)
    (HomologicalComplex.eval C (ComplexShape.up ℕ) p)

private theorem ColumnPageData.unsigned_natural
    {I I' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    {L : DecreasingFiltration (columnTotal I)} {L' : DecreasingFiltration (columnTotal I')}
    {D : FilteredComplexPageDifferential (columnTotal I) L 1}
    {D' : FilteredComplexPageDifferential (columnTotal I') L' 1}
    (A : ColumnPageData I L D) (B : ColumnPageData I' L' D')
    (P : D.page ⟶ D'.page) (f : I ⟶ I') (p : ℕ) (q : ℤ)
    (he : P.f ((p : ℤ), q) ≫ (B.e p q).hom = (A.e p q).hom ≫
      HomologicalComplex.homologyMap
        (((HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℕ)).map f).f p)
        q) :
    P.f ((p : ℤ), q) ≫ (B.unsigned p q).hom =
      (A.unsigned p q).hom ≫ (HomologicalComplex.homologyMap f q).f p := by
  dsimp only [ColumnPageData.unsigned, Iso.trans_hom, Preadditive.smul_iso_hom]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp]
  rw [← Category.assoc, he, Category.assoc, column_eval_homology_map]
  simp only [Category.assoc]
/-- The image of the canonical map between adjacent two-column quotients is
vertical cohomology of horizontal cohomology, naturally for maps of bicomplexes.
Source: Stacks Project, Homology, Tag 0130, Lemma 12.25.1, clauses (2), (4), (6),
and Tag 012K, the quotient-complex image description of filtered pages.
(blueprint: lem-sp-second-filtration-two-column-image).

Proof.
Extend the natural-number degree by zero. The diagonal inclusion with second
index p, followed by projection modulo the next filtration step, identifies
that graded complex with the horizontal complex in degree p, shifted by p.
On horizontal cohomology in degree q the remaining total differential is
(-1)^q times the vertical differential. Conjugation in vertical degree p by
(-1)^(p*q) removes this sign.

Use the two adjacent short exact sequences of column quotients. A horizontal
cohomology class lifts to H^(p+q)(L^p/L^(p+2)) precisely when its vertical
image is a horizontal boundary: lifting supplies the correcting component in
column p+1. The kernel of the resulting map to H^(p+q)(L^(p-1)/L^(p+1))
consists precisely of vertical boundaries: a primitive has a component in
column p-1, whose horizontal differential vanishes and whose vertical
differential represents that boundary. Thus the image of the displayed map
is the kernel of the induced vertical differential modulo its image, which
is H^p(H^q(I)). Kernel and cokernel universal properties give the isomorphism.
At p=0 the incoming extended column is zero, so the same argument computes
the kernel without an incoming boundary. At q=0 the negative horizontal
column is zero, giving the same horizontal cohomology description.

For a map f of bicomplexes, totalization commutes with the diagonal inclusions,
column projections, and both differentials. It also commutes with the sign
multipliers. Hence the induced morphisms in the two adjacent short exact
sequences commute with the kernel/cokernel identifications just constructed.
The equations for s and b uniquely specify the induced map on the target
quotient, since step inclusions are monic and quotient projections are epic.
This gives the stated naturality equation after composing with the canonical
inclusion of the cohomology image in target quotient cohomology. -/
theorem secondFiltration_two_column_image
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    {ι : Type uI}
    (I : ι → HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ (a : ι) (k : ℤ), k < 0 → IsZero ((I a).X k))
    (L : ∀ a : ι, DecreasingFiltration
      (HomologicalComplex₂.total
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (I a)) (ComplexShape.up ℤ)))
    (hL : ∀ (a : ι) (p n : ℤ), (L a).complexStep p n =
      ((HomologicalComplex₂.secondFiltration
        (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (I a)) n).step p))
    (φ : ∀ (a : ι) (p : ℕ),
      (L a).complexQuotient (p : ℤ) ((p : ℤ) + 2) (by omega) ⟶
        (L a).complexQuotient ((p : ℤ) - 2 + 1) ((p : ℤ) + 1) (by omega))
    (hφ : ∀ (a : ι) (p : ℕ),
      (L a).complexQuotientπ (p : ℤ) ((p : ℤ) + 2) (by omega) ≫ φ a p =
        Subobject.ofLE ((L a).step (p : ℤ)) ((L a).step ((p : ℤ) - 2 + 1))
          ((L a).antitone_step (by omega)) ≫
            (L a).complexQuotientπ ((p : ℤ) - 2 + 1) ((p : ℤ) + 1) (by omega)) :
    ∃ e : ∀ (a : ι) (p q : ℕ),
        image (HomologicalComplex.homologyMap (φ a p) ((p : ℤ) + (q : ℤ))) ≅
          ((I a).homology (q : ℤ)).homology p,
      ∀ (a b : ι) (f : I a ⟶ I b) (p q : ℕ)
        (s : ((L a).step ((p : ℤ) - 2 + 1) : CochainComplex C ℤ) ⟶
          ((L b).step ((p : ℤ) - 2 + 1) : CochainComplex C ℤ))
        (β : (L a).complexQuotient ((p : ℤ) - 2 + 1) ((p : ℤ) + 1) (by omega) ⟶
          (L b).complexQuotient ((p : ℤ) - 2 + 1) ((p : ℤ) + 1) (by omega)),
        s ≫ ((L b).step ((p : ℤ) - 2 + 1)).arrow =
          ((L a).step ((p : ℤ) - 2 + 1)).arrow ≫ HomologicalComplex₂.total.map
            (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f) (ComplexShape.up ℤ) →
        (L a).complexQuotientπ ((p : ℤ) - 2 + 1) ((p : ℤ) + 1) (by omega) ≫ β =
          s ≫ (L b).complexQuotientπ ((p : ℤ) - 2 + 1) ((p : ℤ) + 1) (by omega) →
        (e a p q).inv ≫
            image.ι (HomologicalComplex.homologyMap (φ a p) ((p : ℤ) + (q : ℤ))) ≫
            HomologicalComplex.homologyMap β ((p : ℤ) + (q : ℤ)) =
          HomologicalComplex.homologyMap (HomologicalComplex.homologyMap f (q : ℤ)) p ≫
            (e b p q).inv ≫
              image.ι (HomologicalComplex.homologyMap (φ b p) ((p : ℤ) + (q : ℤ))) := by
  classical
  let E := (ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let K (a : ι) := columnTotal (I a)
  let D (a : ι) (r : ℤ) (hr : 1 ≤ r) : FilteredComplexPageDifferential (K a) (L a) r :=
    (filteredComplex_page_differential_exists_unique (K a) (L a) r hr).choose
  let A (a : ι) := makeColumnPageData (I a) (hzero a) (L a) (hL a) (D a 1 (by omega))
  let T (a : ι) (p q : ℕ) :=
    makeTwoColumnImageData (K a) (L a) (p : ℤ) (q : ℤ) (φ a p) (hφ a p)
  have hex (a : ι) (p q : ℕ) :
      ∃! e : (D a 1 (by omega)).page.homology ((p : ℤ), (q : ℤ)) ≅
          filteredComplexPageObject (K a) (L a) 2 ((p : ℤ), (q : ℤ)),
        FilteredComplexHomologyNormalized (K a) (L a) 1 (D a 1 (by omega))
          ((p : ℤ), (q : ℤ)) e := by
    have H := filteredComplex_normalized_homology (K a) (L a) 1 (by omega)
      (D a 1 (by omega)) ((p : ℤ), (q : ℤ))
    exact H
  choose N hN using fun a p q ↦ (hex a p q).exists
  let e (a : ι) (p q : ℕ) :=
    (T a p q).e.symm ≪≫ (N a p q).symm ≪≫ (A a).homologyIso (hL a) p (q : ℤ)
  refine ⟨e, ?_⟩
  intro a b f p q s₀ β hs₀ hβ₀
  let u := HomologicalComplex₂.total.map (E.map f) (ComplexShape.up ℤ)
  obtain ⟨tf, htf⟩ := total_secondFiltration_map (columnExtension (I a))
    (columnExtension (I b)) (L a) (L b) (hL a) (hL b) (E.map f)
  choose s hs' using tf.preserves
  have hs (i : ℤ) : s i ≫ ((L b).step i).arrow = ((L a).step i).arrow ≫ u := by
    simpa only [htf] using hs' i
  have hss : s₀ = s ((p : ℤ) - 2 + 1) := by
    apply (cancel_mono ((L b).step ((p : ℤ) - 2 + 1)).arrow).1
    exact hs₀.trans (hs _).symm
  have hβ : (L a).complexQuotientπ ((p : ℤ) - 2 + 1) ((p : ℤ) + 1) (by omega) ≫ β =
      s ((p : ℤ) - 2 + 1) ≫
        (L b).complexQuotientπ ((p : ℤ) - 2 + 1) ((p : ℤ) + 1) (by omega) := by
    simpa only [hss] using hβ₀
  obtain ⟨v, g, P, hv, hg, hm⟩ :=
    natural_filtered_pages (K a) (K b) (L a) (L b) u s hs (D a) (D b)
  have hrow (i : ℕ) :
      (P 1 (by omega)).f ((i : ℤ), (q : ℤ)) ≫ ((A b).e i (q : ℤ)).hom =
        ((A a).e i (q : ℤ)).hom ≫
          HomologicalComplex.homologyMap
            (((HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ)
              (ComplexShape.up ℕ)).map f).f i) (q : ℤ) := by
    apply normalized_first_page_natural (K a) (K b)
      ((I a).flip.X i) ((I b).flip.X i) (L a) (L b) (i : ℤ) (q : ℤ) u
      (((HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ)
        (ComplexShape.up ℕ)).map f).f i) (s (i : ℤ)) (hs (i : ℤ))
      _ _ (by simpa only [u, E, HomologicalComplex₂.flipFunctor, Category.assoc] using
        column_total_inclusion_natural f i (q : ℤ))
      (v (i : ℤ) ((i : ℤ) + (q : ℤ))) (hv _ _)
      (g 1 (by omega) ((i : ℤ), (q : ℤ))) (hg 1 (by omega) _)
      ((P 1 (by omega)).f ((i : ℤ), (q : ℤ))) (hm 1 (by omega) _)
      ((A a).t i (q : ℤ)) ((A b).t i (q : ℤ))
      ((A a).ht i (q : ℤ)) ((A b).ht i (q : ℤ))
      ((A a).x i (q : ℤ)) ((A b).x i (q : ℤ))
      ((A a).hx i (q : ℤ)) ((A b).hx i (q : ℤ))
      ((A a).e i (q : ℤ)) ((A b).e i (q : ℤ))
      ((A a).he i (q : ℤ)) ((A b).he i (q : ℤ))
  have hu (i : ℕ) := (A a).unsigned_natural (A b) (P 1 (by omega)) f i (q : ℤ) (hrow i)
  have hH := (A a).homologyIso_natural (A b) (hL a) (hL b)
    (P 1 (by omega)) f p (q : ℤ) hu
  have hn := normalized_page_two_natural (K a) (K b) (L a) (L b)
    (D a 1 (by omega)) (D b 1 (by omega)) (P 1 (by omega)) ((p : ℤ), (q : ℤ))
  have hn' := hn (N a p q) (N b p q) (hN a p q) (hN b p q)
    (v (p : ℤ) ((p : ℤ) + (q : ℤ)))
    (g 1 (by omega) ((p : ℤ), (q : ℤ))) (g 2 (by omega) ((p : ℤ), (q : ℤ)))
    ((P 2 (by omega)).f ((p : ℤ), (q : ℤ)))
    (hg 1 (by omega) _) (hg 2 (by omega) _) (hm 1 (by omega) _) (hm 2 (by omega) _)
  have hi := (T a p q).natural (T b p q) (hφ a p) (hφ b p) u s hs β hβ
    (v (p : ℤ) ((p : ℤ) + (q : ℤ))) (hv _ _)
    (g 2 (by omega) ((p : ℤ), (q : ℤ))) (hg 2 (by omega) _)
    ((P 2 (by omega)).f ((p : ℤ), (q : ℤ))) (hm 2 (by omega) _)
  have hinv : ((A a).homologyIso (hL a) p (q : ℤ)).inv ≫
        HomologicalComplex.homologyMap (P 1 (by omega)) ((p : ℤ), (q : ℤ)) =
      HomologicalComplex.homologyMap (HomologicalComplex.homologyMap f (q : ℤ)) p ≫
        ((A b).homologyIso (hL b) p (q : ℤ)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hH, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  calc
    _ = ((A a).homologyIso (hL a) p (q : ℤ)).inv ≫ (N a p q).hom ≫
        (P 2 (by omega)).f ((p : ℤ), (q : ℤ)) ≫ (T b p q).e.hom ≫
          image.ι (HomologicalComplex.homologyMap (φ b p) ((p : ℤ) + (q : ℤ))) := by
      dsimp only [e, Iso.trans_inv, Iso.symm_inv]
      simpa only [Category.assoc] using congrArg
        (fun t ↦ ((A a).homologyIso (hL a) p (q : ℤ)).inv ≫ (N a p q).hom ≫ t) hi.symm
    _ = ((A a).homologyIso (hL a) p (q : ℤ)).inv ≫
        HomologicalComplex.homologyMap (P 1 (by omega)) ((p : ℤ), (q : ℤ)) ≫
          (N b p q).hom ≫ (T b p q).e.hom ≫
            image.ι (HomologicalComplex.homologyMap (φ b p) ((p : ℤ) + (q : ℤ))) := by
      simpa only [Category.assoc] using congrArg
        (fun t ↦ ((A a).homologyIso (hL a) p (q : ℤ)).inv ≫ t ≫ (T b p q).e.hom ≫
          image.ι (HomologicalComplex.homologyMap (φ b p) ((p : ℤ) + (q : ℤ)))) hn'.symm
    _ = HomologicalComplex.homologyMap (HomologicalComplex.homologyMap f (q : ℤ)) p ≫
        ((A b).homologyIso (hL b) p (q : ℤ)).inv ≫ (N b p q).hom ≫ (T b p q).e.hom ≫
          image.ι (HomologicalComplex.homologyMap (φ b p) ((p : ℤ) + (q : ℤ))) := by
      simpa only [Category.assoc] using congrArg
        (fun t ↦ t ≫ (N b p q).hom ≫ (T b p q).e.hom ≫
          image.ι (HomologicalComplex.homologyMap (φ b p) ((p : ℤ) + (q : ℤ)))) hinv
    _ = _ := by
      dsimp only [e, Iso.trans_inv, Iso.symm_inv]
      simp only [Category.assoc]
end CategoryTheory
