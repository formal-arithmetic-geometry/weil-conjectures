/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup

/-! # Convergence of localized finite filtered complexes

Source: Stacks Project, Homology, Tags 012P and 012W.
(blueprint: lem-kun-localized-filtered-convergence).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Restriction commutes with inclusion of a filtration step.
Source: Stacks, Tag 0121 (blueprint: lem-kun-localized-filtered-convergence). -/
theorem kunneth_step_arrow {K L : FilteredObject C} (f : K ⟶ L) (a : ℤ) :
    FilteredObject.restrictionSteps f a ≫ (L.filtration.F a).arrow =
      (K.filtration.F a).arrow ≫ f.hom :=
  Classical.choose_spec (f.preserves a)

/-- Associated-graded maps commute with the quotient projection.
Source: Stacks, Tag 0121 (blueprint: lem-kun-localized-filtered-convergence). -/
theorem kunneth_graded_projection {K L : FilteredObject C} (f : K ⟶ L) (a : ℤ) :
    cokernel.π (Subobject.ofLE _ _ (K.filtration.F_succ_le a)) ≫
        FilteredObject.gradedMapSteps f a =
      FilteredObject.restrictionSteps f a ≫
        cokernel.π (Subobject.ofLE _ _ (L.filtration.F_succ_le a)) :=
  Classical.choose_spec (FilteredObject.exists_gradedMap_steps K L f a)

/-- Taking an associated graded piece is a functor.
Source: Stacks, Tag 0121 (blueprint: lem-kun-localized-filtered-convergence). -/
def kunnethGradedFunctor (C : Type u) [Category.{v} C] [Abelian C] (a : ℤ) :
    FilteredObject C ⥤ C where
  obj K := K.filtration.gr a
  map f := FilteredObject.gradedMapSteps f a
  map_id K := by
    apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (K.filtration.F_succ_le a)))).1
    rw [kunneth_graded_projection]
    have hr : FilteredObject.restrictionSteps (𝟙 K) a = 𝟙 _ := by
      apply (cancel_mono (K.filtration.F a).arrow).1
      rw [kunneth_step_arrow]
      change (K.filtration.F a).arrow ≫ 𝟙 _ = 𝟙 _ ≫ (K.filtration.F a).arrow
      simp only [Category.comp_id, Category.id_comp]
    rw [hr, Category.id_comp]
    exact (Category.comp_id _).symm
  map_comp {K L M} f g := by
    have hr : FilteredObject.restrictionSteps (f ≫ g) a =
        FilteredObject.restrictionSteps f a ≫ FilteredObject.restrictionSteps g a := by
      apply (cancel_mono (M.filtration.F a).arrow).1
      rw [kunneth_step_arrow, Category.assoc, kunneth_step_arrow,
        ← Category.assoc, kunneth_step_arrow, Category.assoc]
      rfl
    apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (K.filtration.F_succ_le a)))).1
    rw [kunneth_graded_projection, hr, Category.assoc,
      ← kunneth_graded_projection, ← Category.assoc, ← kunneth_graded_projection]
    exact Category.assoc _ _ _

/-- Finiteness of a filtration is invariant under filtered isomorphism.
Source: Stacks, Tag 0121 (blueprint: lem-kun-localized-filtered-convergence).
Proof. The filtration restrictions of an isomorphism are isomorphisms: their composites
are identities by uniqueness of factorization through subobject inclusions. At a lower
bound the inclusion is therefore an isomorphism, and at an upper bound its source is zero. -/
theorem kunneth_filtered_finite_iso {K L : FilteredObject C} (e : K ≅ L)
    (h : K.filtration.IsFinite) : L.filtration.IsFinite := by
  let forget : FilteredObject C ⥤ C := { obj K := K.obj, map f := f.hom }
  have hi : IsIso e.hom.hom := (forget.mapIso e).isIso_hom
  have hrest (a : ℤ) : IsIso (FilteredObject.restrictionSteps e.hom a) := by
    have hcomp {K L M : FilteredObject C} (f : K ⟶ L) (g : L ⟶ M) :
        FilteredObject.restrictionSteps (f ≫ g) a =
          FilteredObject.restrictionSteps f a ≫ FilteredObject.restrictionSteps g a := by
      apply (cancel_mono (M.filtration.F a).arrow).1
      rw [kunneth_step_arrow, Category.assoc, kunneth_step_arrow,
        ← Category.assoc, kunneth_step_arrow, Category.assoc]
      rfl
    have hid (K : FilteredObject C) : FilteredObject.restrictionSteps (𝟙 K) a = 𝟙 _ := by
      apply (cancel_mono (K.filtration.F a).arrow).1
      rw [kunneth_step_arrow]
      change (K.filtration.F a).arrow ≫ 𝟙 _ = 𝟙 _ ≫ (K.filtration.F a).arrow
      simp only [Category.comp_id, Category.id_comp]
    exact ⟨⟨FilteredObject.restrictionSteps e.inv a,
      by rw [← hcomp, e.hom_inv_id, hid], by rw [← hcomp, e.inv_hom_id, hid]⟩⟩
  obtain ⟨a, b, ha, hb⟩ := h
  refine ⟨a, b, ?_, ?_⟩
  · have hiK : IsIso (K.filtration.F a).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 ha
    have hEq : (L.filtration.F a).arrow =
        inv (FilteredObject.restrictionSteps e.hom a) ≫
          (K.filtration.F a).arrow ≫ e.hom.hom := by
      rw [← kunneth_step_arrow, IsIso.inv_hom_id_assoc]
    apply (Subobject.isIso_arrow_iff_eq_top _).1
    rw [hEq]
    infer_instance
  · have hzK : IsZero (K.filtration.F b : C) := by
      rw [hb]
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    have hzL : IsZero (L.filtration.F b : C) :=
      hzK.of_iso (asIso (FilteredObject.restrictionSteps e.hom b)).symm
    have hz : (L.filtration.F b).arrow = 0 := hzL.eq_of_src _ _
    simpa only [Subobject.mk_arrow] using (Subobject.mk_eq_bot_iff_zero).2 hz

/-- All convergence comparisons for the localized finite filtered page functor.
Source: Stacks, Tags 012P and 012W
(blueprint: lem-kun-localized-filtered-convergence). -/
structure LocalizedFilteredConvergenceData (R : Type u) [CommRing R]
    (d : FilteredPageLocalizationData R) where
  finite : ∀ (X : finiteFilteredModuleDerivedCategory R) (n : ℤ),
    ((d.Hbar n).obj X).filtration.IsFinite
  bound : finiteFilteredModuleDerivedCategory R → ℤ → ℤ → ℤ
  bound_ge : ∀ X n a, 1 ≤ bound X n a
  comparison : ∀ (X : finiteFilteredModuleDerivedCategory R) (n a t : ℤ)
      (ht : 1 ≤ t) (_hs : bound X n a ≤ t),
    ((d.Hbar n).obj X).filtration.gr a ≅ ((d.Sbar.obj X).page t ht).X (a, n - a)
  differential : ∀ (X : finiteFilteredModuleDerivedCategory R) (n a t : ℤ)
      (ht : 1 ≤ t), bound X n a ≤ t →
    ((d.Sbar.obj X).page t ht).dFrom (a, n - a) = 0 ∧
      ((d.Sbar.obj X).page t ht).dTo (a, n - a) = 0
  naturality : ∀ {X Y : finiteFilteredModuleDerivedCategory R} (f : X ⟶ Y)
      (n a t : ℤ) (ht : 1 ≤ t) (hX : bound X n a ≤ t) (hY : bound Y n a ≤ t),
    FilteredObject.gradedMapSteps ((d.Hbar n).map f) a ≫ (comparison Y n a t ht hY).hom =
      (comparison X n a t ht hX).hom ≫ ((d.Sbar.map f).hom t ht).f (a, n - a)
  successor : ∀ (X : finiteFilteredModuleDerivedCategory R) (n a t : ℤ)
      (ht : 1 ≤ t) (hs : bound X n a ≤ t),
    ((d.Sbar.obj X).page t ht).iCycles (a, n - a) ≫
        (comparison X n a t ht hs).inv =
      ((d.Sbar.obj X).page t ht).homologyπ (a, n - a) ≫
        ((d.Sbar.obj X).iso t (t + 1) (a, n - a) rfl ht).hom ≫
          (comparison X n a (t + 1) (by omega) (by omega)).inv

private def representativeComparison {R : Type u} [CommRing R]
    (d : FilteredPageLocalizationData R) (U : CochainComplex.FiniteFilteredModuleComplex R)
    (a b t : ℤ) (ht : 1 ≤ t) (hs : d.bound U a b ≤ t) :
    (kunnethGradedFunctor (ModuleCat R) a).obj
      ((finiteFilteredCohomology R (a + b)).obj U) ≅
      (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) :=
  ((d.comparison U a b t ht hs).pageToImage ≪≫
    (d.comparison U a b t ht hs).imageToGraded).symm

private theorem representativeComparison_naturality {R : Type u} [CommRing R]
    (d : FilteredPageLocalizationData R)
    {U V : CochainComplex.FiniteFilteredModuleComplex R}
    (α : (finiteFilteredDerivedQuotient R).obj U ⟶ (finiteFilteredDerivedQuotient R).obj V)
    (a b t : ℤ) (ht : 1 ≤ t) (hU : d.bound U a b ≤ t) (hV : d.bound V a b ≤ t) :
    FilteredObject.gradedMapSteps
        (finiteFilteredDescendedMap R (finiteFilteredCohomology R (a + b))
          (d.Hbar (a + b)) (d.eH (a + b)) α) a ≫
        (representativeComparison d V a b t ht hV).hom =
      (representativeComparison d U a b t ht hU).hom ≫
        ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R)
          d.Sbar d.eS α).hom t ht).f (a, b) := by
  let cU := d.comparison U a b t ht hU
  let cV := d.comparison V a b t ht hV
  have hn := d.stationary_naturality α a b t ht hU hV
  have hg := d.stationary_graded_naturality α a b t ht hU hV
  have hsq : ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R)
        d.Sbar d.eS α).hom t ht).f (a, b) ≫
        cV.pageToImage.hom ≫ cV.imageToGraded.hom =
      cU.pageToImage.hom ≫ cU.imageToGraded.hom ≫
        FilteredObject.gradedMapSteps
          (finiteFilteredDescendedMap R (finiteFilteredCohomology R (a + b))
            (d.Hbar (a + b)) (d.eH (a + b)) α) a := by
    dsimp only [cU, cV]
    calc
      _ = _ := congrArg (fun z ↦ z ≫ (d.comparison V a b t ht hV).imageToGraded.hom) hn
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg ((d.comparison U a b t ht hU).pageToImage.hom ≫ ·) hg
  apply (cancel_mono (cV.pageToImage.hom ≫ cV.imageToGraded.hom)).1
  dsimp only [representativeComparison, Iso.symm_hom, Iso.trans_inv, cU, cV] at *
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hsq]
  simp only [Iso.inv_hom_id_assoc]

private theorem representativeComparison_successor {R : Type u} [CommRing R]
    (d : FilteredPageLocalizationData R) (U : CochainComplex.FiniteFilteredModuleComplex R)
    (a b t : ℤ) (ht : 1 ≤ t) (hs : d.bound U a b ≤ t) :
    (((finiteFilteredPageFunctor R).obj U).page t ht).iCycles (a, b) ≫
        (representativeComparison d U a b t ht hs).inv =
      (((finiteFilteredPageFunctor R).obj U).page t ht).homologyπ (a, b) ≫
        (((finiteFilteredPageFunctor R).obj U).iso t (t + 1) (a, b) rfl ht).hom ≫
          (representativeComparison d U a b (t + 1) (by omega) (by omega)).inv := by
  dsimp only [representativeComparison, Iso.symm_inv, Iso.trans_hom]
  rw [← Category.assoc, d.successor_agreement, Category.assoc,
    d.successor_graded_agreement]
  simp only [Category.assoc]

private theorem representative_finite {R : Type u} [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (n : ℤ) :
    (finiteFilteredCohomologyFiltration R U n).IsFinite := by
  obtain ⟨G, X, L, A, aH, eD, eC, hG, hfinite, _⟩ :=
    (finiteFilteredPageModel R).abutment_spec U
  have he : finiteFilteredCohomologyFiltration R U n = G n := by
    have hf : (finiteFilteredCohomologyFiltration R U n).F = (G n).F := by
      funext a
      exact (hG n a).symm
    cases hF : finiteFilteredCohomologyFiltration R U n
    cases hG' : G n
    simp only [hF, hG'] at hf
    cases hf
    rfl
  rw [he]
  exact (hfinite n).1

private def representativeComparisonN {R : Type u} [CommRing R]
    (d : FilteredPageLocalizationData R) (U : CochainComplex.FiniteFilteredModuleComplex R)
    (n a b t : ℤ) (hn : n = a + b) (ht : 1 ≤ t) (hs : d.bound U a b ≤ t) :
    (kunnethGradedFunctor (ModuleCat R) a).obj
      ((finiteFilteredCohomology R n).obj U) ≅
      (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) :=
  eqToIso (congrArg (fun n ↦ (kunnethGradedFunctor (ModuleCat R) a).obj
      ((finiteFilteredCohomology R n).obj U)) hn) ≪≫
      representativeComparison d U a b t ht hs

private theorem representativeComparisonN_naturality {R : Type u} [CommRing R]
    (d : FilteredPageLocalizationData R)
    {U V : CochainComplex.FiniteFilteredModuleComplex R}
    (α : (finiteFilteredDerivedQuotient R).obj U ⟶ (finiteFilteredDerivedQuotient R).obj V)
    (n a b t : ℤ) (hn : n = a + b) (ht : 1 ≤ t) (hU : d.bound U a b ≤ t)
    (hV : d.bound V a b ≤ t) :
    FilteredObject.gradedMapSteps
        (finiteFilteredDescendedMap R (finiteFilteredCohomology R n)
          (d.Hbar n) (d.eH n) α) a ≫
        (representativeComparisonN d V n a b t hn ht hV).hom =
      (representativeComparisonN d U n a b t hn ht hU).hom ≫
        ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R)
          d.Sbar d.eS α).hom t ht).f (a, b) := by
  subst n
  simpa only [representativeComparisonN, eqToIso_refl, Iso.refl_trans] using
    representativeComparison_naturality d α a b t ht hU hV

private theorem representativeComparisonN_successor {R : Type u} [CommRing R]
    (d : FilteredPageLocalizationData R) (U : CochainComplex.FiniteFilteredModuleComplex R)
    (n a b t : ℤ) (hn : n = a + b) (ht : 1 ≤ t) (hs : d.bound U a b ≤ t) :
    (((finiteFilteredPageFunctor R).obj U).page t ht).iCycles (a, b) ≫
        (representativeComparisonN d U n a b t hn ht hs).inv =
      (((finiteFilteredPageFunctor R).obj U).page t ht).homologyπ (a, b) ≫
        (((finiteFilteredPageFunctor R).obj U).iso t (t + 1) (a, b) rfl ht).hom ≫
          (representativeComparisonN d U n a b (t + 1) hn (by omega) (by omega)).inv := by
  subst n
  simpa only [representativeComparisonN, eqToIso_refl, Iso.refl_trans] using
    representativeComparison_successor d U a b t ht hs

private theorem spectral_successor_transport {C : Type u} [Category.{v} C] [Abelian C]
    {E E' : CohomologicalSpectralSequence C 1} (e : E ≅ E') {A B : C} (u : A ≅ B)
    (i : ℤ × ℤ) (t : ℤ) (ht : 1 ≤ t)
    (c : B ≅ (E'.page t ht).X i) (c' : B ≅ (E'.page (t + 1) (by omega)).X i)
    (h : (E'.page t ht).iCycles i ≫ c.inv =
      (E'.page t ht).homologyπ i ≫ (E'.iso t (t + 1) i rfl ht).hom ≫ c'.inv) :
    (E.page t ht).iCycles i ≫ (e.hom.hom t ht).f i ≫ c.inv ≫ u.inv =
      (E.page t ht).homologyπ i ≫ (E.iso t (t + 1) i rfl ht).hom ≫
        (e.hom.hom (t + 1) (by omega)).f i ≫ c'.inv ≫ u.inv := by
  rw [← HomologicalComplex.cyclesMap_i_assoc]
  have hh := congrArg (· ≫ u.inv) h
  simp only [Category.assoc] at hh
  rw [hh, ← HomologicalComplex.homologyπ_naturality_assoc,
    e.hom.comm_assoc t (t + 1) i rfl ht]

/-- Finite filtered convergence survives localization, including its coherent stationary
comparisons and their naturality for arbitrary localized morphisms.
Source: Stacks, Tags 012P and 012W; the descent interfaces of Tags 05S2 and 05S3
(blueprint: lem-kun-localized-filtered-convergence).

Proof. Choose a finite filtered representative of each localized object. The normalized
page model gives eventual zero incoming and outgoing differentials; increase its bound
by the stationary-window bound in `d`. Compose `pageToImage` with `imageToGraded`, then
invert, to obtain the graded-to-page comparison. The two stationary naturality squares
in `d` prove its naturality for every localized morphism between representatives. The
successor equation follows from `successor_agreement` and `successor_graded_agreement`.
Transport these maps along the isomorphism from the chosen representative to the given
object, using `eS` and `eH`. The functor laws conjugate any morphism to a morphism between
representatives; homology naturality transports the successor equation. Finally the
image filtration on representative cohomology is finite, so the same holds after transport. -/
theorem localizedFilteredConvergence (R : Type u) [CommRing R]
    (d : FilteredPageLocalizationData R) : Nonempty (LocalizedFilteredConvergenceData R d) := by
  classical
  let U (X : finiteFilteredModuleDerivedCategory R) :
      CochainComplex.FiniteFilteredModuleComplex R := X.as.obj.as
  have hU (X : finiteFilteredModuleDerivedCategory R) :
      (finiteFilteredDerivedQuotient R).obj (U X) = X := rfl
  let eH (X : finiteFilteredModuleDerivedCategory R) (n : ℤ) :
      (d.Hbar n).obj X ≅ (finiteFilteredCohomology R n).obj (U X) := (d.eH n).app (U X)
  let eS (X : finiteFilteredModuleDerivedCategory R) :
      d.Sbar.obj X ≅ (finiteFilteredPageFunctor R).obj (U X) := d.eS.app (U X)
  let P (t : ℤ) (ht : 1 ≤ t) (i : ℤ × ℤ) :=
    SpectralSequence.pageFunctor (ModuleCat R) (fun r ↦ ComplexShape.up' (r, 1 - r))
      1 t ht ⋙ HomologicalComplex.eval _ _ i
  have hstab (X : finiteFilteredModuleDerivedCategory R) (n a : ℤ) :=
    (finiteFilteredPageModel R).stabilize_spec (U X) a (n - a)
  choose T hT htSpec using hstab
  let N (X : finiteFilteredModuleDerivedCategory R) (n a : ℤ) :=
    max (T X n a) (d.bound (U X) a (n - a))
  let cmp (X : finiteFilteredModuleDerivedCategory R) (n a t : ℤ)
      (ht : 1 ≤ t) (hs : N X n a ≤ t) :=
    (kunnethGradedFunctor (ModuleCat R) a).mapIso (eH X n) ≪≫
      representativeComparisonN d (U X) n a (n - a) t (by omega) ht
        (le_trans (le_max_right _ _) hs) ≪≫
        (P t ht (a, n - a)).mapIso (eS X).symm
  refine ⟨{
    finite := ?_
    bound := N
    bound_ge := ?_
    comparison := cmp
    differential := ?_
    naturality := ?_
    successor := ?_ }⟩
  · intro X n
    exact kunneth_filtered_finite_iso (eH X n).symm (representative_finite (U X) n)
  · intro X n a
    exact (hT X n a).trans (le_max_left _ _)
  · intro X n a t ht hs
    have hd := (htSpec X n a t (le_trans (le_max_left _ _) hs)).2.2
    have hout := hd.1
    have hin := hd.2.1
    have hrel : (ComplexShape.up' (t, 1 - t)).Rel (a, n - a)
        (a + t, (n - a) - t + 1) := by
      change (a, n - a) + (t, 1 - t) = (a + t, n - a - t + 1)
      apply Prod.ext
      · rfl
      · change n - a + (1 - t) = n - a - t + 1
        omega
    have hrel' : (ComplexShape.up' (t, 1 - t)).Rel
        (a - t, (n - a) + t - 1) (a, n - a) := by
      change (a - t, n - a + t - 1) + (t, 1 - t) = (a, n - a)
      apply Prod.ext
      · change a - t + t = a
        omega
      · change n - a + t - 1 + (1 - t) = n - a
        omega
    change (((finiteFilteredPageFunctor R).obj (U X)).page t ht).d
      (a, n - a) (a + t, n - a - t + 1) = 0 at hout
    change (((finiteFilteredPageFunctor R).obj (U X)).page t ht).d
      (a - t, n - a + t - 1) (a, n - a) = 0 at hin
    have hf : (((finiteFilteredPageFunctor R).obj (U X)).page t ht).dFrom
        (a, n - a) = 0 := by rw [HomologicalComplex.dFrom_eq _ hrel, hout, zero_comp]
    have hi : (((finiteFilteredPageFunctor R).obj (U X)).page t ht).dTo
        (a, n - a) = 0 := by rw [HomologicalComplex.dTo_eq _ hrel', hin, comp_zero]
    let ep := (SpectralSequence.pageFunctor _ _ 1 t ht).mapIso (eS X)
    constructor
    · apply (cancel_mono (ep.hom.f ((ComplexShape.up' (t, 1 - t)).next
        (a, n - a)))).1
      calc
        _ = ep.hom.f (a, n - a) ≫
            (((finiteFilteredPageFunctor R).obj (U X)).page t ht).dFrom
              (a, n - a) := (ep.hom.comm _ _).symm
        _ = 0 := by rw [hf, comp_zero]
        _ = _ := zero_comp.symm
    · apply (cancel_mono (ep.hom.f (a, n - a))).1
      calc
        _ = ep.hom.f ((ComplexShape.up' (t, 1 - t)).prev (a, n - a)) ≫
            (((finiteFilteredPageFunctor R).obj (U X)).page t ht).dTo
              (a, n - a) := (ep.hom.comm _ _).symm
        _ = 0 := by rw [hi, comp_zero]
        _ = _ := zero_comp.symm
  · intro X Y f n a t ht hX hY
    let K := kunnethGradedFunctor (ModuleCat R) a
    have hn := representativeComparisonN_naturality d
      (show (finiteFilteredDerivedQuotient R).obj (U X) ⟶
        (finiteFilteredDerivedQuotient R).obj (U Y) from f) n a (n - a) t (by omega) ht
      (le_trans (le_max_right _ _) hX) (le_trans (le_max_right _ _) hY)
    apply (cancel_epi (K.mapIso (eH X n)).inv).1
    apply (cancel_mono ((P t ht (a, n - a)).mapIso (eS Y)).hom).1
    dsimp only [cmp, K, Iso.trans_hom]
    simp only [Functor.mapIso_symm, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [finiteFilteredDescendedMap] at hn
    change K.map ((eH X n).inv ≫ (d.Hbar n).map f ≫ (eH Y n).hom) ≫ _ =
      _ ≫ ((eS X).inv ≫ d.Sbar.map f ≫ (eS Y).hom |>.hom t ht).f (a, n - a) at hn
    simp only [K.map_comp, SpectralSequence.comp_hom, HomologicalComplex.comp_f,
      Category.assoc] at hn
    simpa only [K, kunnethGradedFunctor, P, Functor.comp_map,
      Functor.mapIso_hom, Functor.mapIso_inv, SpectralSequence.pageFunctor_map,
      HomologicalComplex.eval_map] using hn
  · intro X n a t ht hs
    dsimp only [cmp, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
    exact spectral_successor_transport (eS X)
      ((kunnethGradedFunctor (ModuleCat R) a).mapIso (eH X n)) (a, n - a) t ht
      _ _ (representativeComparisonN_successor d (U X) n a (n - a) t (by omega) ht _)

end CategoryTheory
