/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.Algebra.Homology.ConeHorizontalGradedIso
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.Filtration

/-! # Horizontal filtration of the cone of a first-quadrant total map

Source: Stacks Project, Homology, Tag 012X, the first filtration of a total complex,
with the mapping-cone construction applied columnwise.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- The summands in a nonnegative diagonal jointly generate the integer extension. -/
private theorem coneHorizontalSummand_hom_ext
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (n : ℤ) {Y : C}
    (g : ((K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).X n ⟶ Y)
    (hg : ∀ h : ℕ, h ≤ n.toNat → coneHorizontalSummand K h n ≫ g = 0) : g = 0 := by
  by_cases hn : 0 ≤ n
  · let e := (K.total (ComplexShape.up ℕ)).extendXIso ComplexShape.embeddingUpNat
      (Int.toNat_of_nonneg hn)
    apply (cancel_epi e.inv).1
    rw [CategoryTheory.Limits.comp_zero]
    apply total.hom_ext
    intro i j hij
    have hij' : i + j = n.toNat := hij
    have h := hg i (by omega)
    have hj : n.toNat - i = j := by omega
    simp only [coneHorizontalSummand, dif_pos hn] at h
    rw [hj, K.ιTotalOrZero_eq _ _ _ _ hij] at h
    simpa only [Category.assoc, CategoryTheory.Limits.comp_zero] using h
  · exact (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat n
      (by intro i hi; change (i : ℤ) = n at hi; omega)).eq_zero_of_src g

/-- A map killing a subobject kills every generating map whose image lies in it. -/
private theorem comp_zero_of_image_le
    {D : Type u} [Category.{v} D] [Abelian D] {X Y Z : D} (a : X ⟶ Y)
    (S : Subobject Y) (g : Y ⟶ Z) (ha : imageSubobject a ≤ S)
    (hg : S.arrow ≫ g = 0) : a ≫ g = 0 := by
  have he : (factorThruImageSubobject a ≫ Subobject.ofLE _ S ha) ≫ S.arrow = a := by
    simp
  rw [← he, Category.assoc, hg, CategoryTheory.Limits.comp_zero]

/-- At zero the finite horizontal sum contains all source and target cone terms. -/
private theorem coneHorizontalStep_zero
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (n : ℤ) : coneHorizontalStep f 0 n = ⊤ := by
  let S := coneHorizontalStep f 0 n
  have : Epi S.arrow := CategoryTheory.Preadditive.epi_of_cancel_zero S.arrow (by
    intro Y g hg
    apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
    · rw [CategoryTheory.Limits.comp_zero]
      apply coneHorizontalSummand_hom_ext A (n + 1)
      intro h hh
      by_cases hn : 0 ≤ n + 1
      · have hmem : h ∈ (Finset.range (n + 2).toNat).filter
            (fun h : ℕ ↦ (0 : ℤ) ≤ (h : ℤ)) := by
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · omega
          · omega
        have him : coneHorizontalImage f h n ≤ S :=
          Finset.le_sup (f := fun h ↦ coneHorizontalImage f h n) hmem
        simpa only [Category.assoc, CategoryTheory.Limits.comp_zero,
          CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v] using
          comp_zero_of_image_le _ S g (le_sup_left.trans him) hg
      · simp [coneHorizontalSummand, hn]
    · rw [CategoryTheory.Limits.comp_zero]
      apply coneHorizontalSummand_hom_ext B n
      intro h hh
      by_cases hn : 0 ≤ n
      · have hmem : h ∈ (Finset.range (n + 2).toNat).filter
            (fun h : ℕ ↦ (0 : ℤ) ≤ (h : ℤ)) := by
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · omega
          · omega
        have him : coneHorizontalImage f h n ≤ S :=
          Finset.le_sup (f := fun h ↦ coneHorizontalImage f h n) hmem
        simpa only [Category.assoc, CategoryTheory.Limits.comp_zero] using
          comp_zero_of_image_le _ S g (le_sup_right.trans him) hg
      · simp [coneHorizontalSummand, hn])
  have : IsIso S.arrow := isIso_of_mono_of_epi S.arrow
  exact Subobject.eq_top_of_isIso_arrow S

/-- There is no horizontal index at least n+2 in the degree-n cone. -/
private theorem coneHorizontalStep_finite
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (n : ℤ) : coneHorizontalStep f (n + 2) n = ⊥ := by
  have he : (Finset.range (n + 2).toNat).filter
      (fun h : ℕ ↦ n + 2 ≤ (h : ℤ)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_range] at hh
    omega
  simp [coneHorizontalStep, he]

/-- Nonpositive cutoff indices impose no condition on the natural horizontal index. -/
private theorem coneHorizontalStep_nonpos
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p n : ℤ) (hp : p ≤ 0) : coneHorizontalStep f p n = ⊤ := by
  have he : (Finset.range (n + 2).toNat).filter
      (fun h : ℕ ↦ p ≤ (h : ℤ)) = Finset.range (n + 2).toNat := by
    apply Finset.filter_eq_self.mpr
    intro h _
    omega
  rw [coneHorizontalStep, he]
  have hzero := coneHorizontalStep_zero f n
  simpa [coneHorizontalStep] using hzero

/-- A subcomplex with full image in every degree is the whole complex. -/
private theorem filtration_step_top_of_degreewise
    {D : Type u} [Category.{v} D] [Abelian D]
    {K : CochainComplex D ℤ} (F : DecreasingFiltration K) (p : ℤ)
    (h : ∀ n : ℤ, F.complexStep p n = ⊤) : F.step p = ⊤ := by
  have hcomp : ∀ n : ℤ, IsIso ((F.step p).arrow.f n) := by
    intro n
    apply (Subobject.isIso_iff_mk_eq_top _).mpr
    simpa only [DecreasingFiltration.complexStep, imageSubobject_mono] using h n
  have : IsIso (F.step p).arrow := HomologicalComplex.Hom.isIso_of_components _
  exact Subobject.eq_top_of_isIso_arrow _

/-- Stable antitone degreewise subobjects assemble into a filtration by subcomplexes. -/
private theorem filtration_of_degreewise
    {D : Type u} [Category.{v} D] [Abelian D] (K : CochainComplex D ℤ)
    (S : ℤ → ∀ n : ℤ, Subobject (K.X n))
    (hS : ∀ n, Antitone (fun p ↦ S p n))
    (hd : ∀ p n, (S p (n + 1)).Factors ((S p n).arrow ≫ K.d n (n + 1))) :
    ∃ F : DecreasingFiltration K, ∀ p n, F.complexStep p n = S p n := by
  let d := fun p n ↦ (S p (n + 1)).factorThru
    ((S p n).arrow ≫ K.d n (n + 1)) (hd p n)
  have hd' (p n : ℤ) : d p n ≫ (S p (n + 1)).arrow =
      (S p n).arrow ≫ K.d n (n + 1) := Subobject.factorThru_arrow _ _ _
  have hsq (p n : ℤ) : d p n ≫ d p (n + 1) = 0 := by
    apply (cancel_mono (S p ((n + 1) + 1)).arrow).1
    rw [Category.assoc, hd', ← Category.assoc, hd', Category.assoc,
      K.d_comp_d, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]
  let L := fun p ↦ CochainComplex.of (fun n ↦ (S p n : D)) (d p) (hsq p)
  let i : ∀ p, L p ⟶ K := fun p ↦ CochainComplex.ofHom
    (fun n ↦ (S p n).arrow) (fun n ↦ by
      simpa only [L, CochainComplex.of_d] using (hd' p n).symm)
  have hi (p : ℤ) : Mono (i p) :=
    HomologicalComplex.mono_of_mono_f _ (fun _ ↦ inferInstance)
  let F : DecreasingFiltration K := {
    step := fun p ↦ Subobject.mk (i p)
    antitone_step := by
      intro p q hpq
      let l : L q ⟶ L p := CochainComplex.ofHom
        (fun n ↦ Subobject.ofLE (S q n) (S p n) (hS n hpq)) (by
          intro n
          simp only [L, CochainComplex.of_d]
          apply (cancel_mono (S p (n + 1)).arrow).1
          rw [Category.assoc, hd', ← Category.assoc, Subobject.ofLE_arrow,
            Category.assoc, Subobject.ofLE_arrow, hd'])
      apply Subobject.mk_le_mk_of_comm l
      ext n
      exact Subobject.ofLE_arrow _ }
  refine ⟨F, ?_⟩
  intro p n
  have he : ((Subobject.mk (i p)).arrow).f n =
      ((Subobject.underlyingIso (i p)).hom).f n ≫ (i p).f n := by
    have h := congrArg (fun a : (Subobject.mk (i p) : CochainComplex D ℤ) ⟶ K ↦ a.f n)
      (Subobject.underlyingIso_hom_comp_eq_mk (i p))
    exact h.symm
  change imageSubobject (((Subobject.mk (i p)).arrow).f n) = S p n
  rw [he, imageSubobject_iso_comp]
  change imageSubobject (S p n).arrow = S p n
  rw [imageSubobject_mono, Subobject.mk_arrow]

/-- Increasing the cutoff shrinks the finite set of horizontal generators. -/
private theorem coneHorizontalStep_antitone
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (n : ℤ) : Antitone (fun p ↦ coneHorizontalStep f p n) := by
  intro p q hpq
  apply Finset.sup_mono
  intro h hh
  simp only [Finset.mem_filter] at hh ⊢
  exact ⟨hh.1, hpq.trans hh.2⟩

/-- The horizontal filtration of a total-map cone has column-map cones as its
nonnegative graded pieces and zero graded pieces in negative filtration degrees.
Source: Stacks Project, Homology, Tag 012X, first filtration and its graded complexes.
(blueprint: lem-sp-first-quadrant-vertical-cone-filtration)

Proof: in degree n, the cone is the sum of the source terms in total degree n+1
and the target terms in total degree n. Its p-th step is the sum of summands with
horizontal index at least p. Vertical differentials preserve that index, horizontal
differentials raise it, and the off-diagonal map preserves it. Thus these summands
are subcomplexes. Their inclusions define an antitone subobject filtration. Step 0
is the whole object. Step n+2 is zero: every source horizontal index is at most n+1,
and every target index is at most n. At n=-1 only the source degree-zero term
can remain; below n=-1 the cone is zero, so the bounds also hold for n+2<=0. The quotient
of step p by step p+1, for p >= 0, keeps exactly horizontal index p. Its source
summands are in vertical degree n+1-p, including vertical cone degree -1. Its
remaining differential is the vertical cone differential with the totalization
sign. Put k=n-p and e=(-1)^p. In this graded differential the source and target
vertical differentials are -e*d_A and e*d_B, and the off-diagonal map is f.
Multiply the source summand in degree n by e^(k+1), and the target summand by e^k.
These invertible scalars give a chain isomorphism to the column cone with degrees
reindexed by n-p: the scalars in successive degrees differ by e, and the source
scalar in degree n equals the target scalar in degree n+1. Thus the diagonal
blocks become -d_A and d_B and the off-diagonal block becomes f. Its homology in
degree n is the column cone's homology in degree n-p. If p < 0, successive steps are both
the whole complex, so their quotient and its homology are zero. No quasi-isomorphism
hypothesis enters this construction. -/
theorem firstQuadrant_vertical_cone_filtration
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)),
      (∀ n : ℤ, F.complexStep 0 n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) ∧
      (∀ p n : ℤ, p < 0 → IsZero ((F.gradedPiece p).homology n)) ∧
      (∀ p n : ℤ, 0 ≤ p → Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone
          (HomologicalComplex.extendMap (f.f p.toNat) ComplexShape.embeddingUpNat)).homology
            (n - p))) := by
  obtain ⟨F, hF⟩ := filtration_of_degreewise
    (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat))
    (coneHorizontalStep f) (coneHorizontalStep_antitone f) (coneHorizontal_step_stable f)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro n
    rw [hF, hF]
    exact ⟨coneHorizontalStep_zero f n, coneHorizontalStep_finite f n⟩
  · intro p n hp
    have htop (q : ℤ) (hq : q ≤ 0) : F.step q = ⊤ := by
      apply filtration_step_top_of_degreewise F q
      intro m
      rw [hF]
      exact coneHorizontalStep_nonpos f q m hq
    have he : F.step (p + 1) = F.step p := by rw [htop _ (by omega), htop _ (by omega)]
    have hi : IsIso (Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega))) := by
      exact (Subobject.isoOfEq _ _ he).isIso_hom
    exact (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map_isZero
      (isZero_cokernel_of_epi (Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega))))
  · intro p n hp
    obtain ⟨e⟩ := coneHorizontal_graded_iso f F hF p hp
    exact ⟨(HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).mapIso e ≪≫
      (CochainComplex.ShiftSequence.shiftIso C (-p) n (n - p) (by omega)).app _⟩

end HomologicalComplex₂
