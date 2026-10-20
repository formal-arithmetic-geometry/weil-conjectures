/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Graded quasi-isomorphisms and two-out-of-three

Source: Stacks Project, Derived Categories, Tags 05S1 and 05RM.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

private theorem restriction_arrow {C : Type*} [Category C] [Abelian C]
    {K L : FilteredObject C} (f : K ⟶ L) (i : ℤ) :
    FilteredObject.restrictionSteps f i ≫ (L.filtration.step i).arrow =
      (K.filtration.step i).arrow ≫ f.hom :=
  Classical.choose_spec (f.preserves i)

private theorem graded_projection {C : Type*} [Category C] [Abelian C]
    {K L : FilteredObject C} (f : K ⟶ L) (i : ℤ) :
    cokernel.π (Subobject.ofLE (K.filtration.step (i + 1)) (K.filtration.step i)
      (K.filtration.antitone_step (by omega))) ≫ FilteredObject.gradedMapSteps f i =
    FilteredObject.restrictionSteps f i ≫
      cokernel.π (Subobject.ofLE (L.filtration.step (i + 1)) (L.filtration.step i)
        (L.filtration.antitone_step (by omega))) :=
  Classical.choose_spec (FilteredObject.exists_gradedMap_steps K L f i)

private theorem restriction_id {C : Type*} [Category C] [Abelian C]
    (K : FilteredObject C) (i : ℤ) :
    FilteredObject.restrictionSteps (𝟙 K) i = 𝟙 _ := by
  apply (cancel_mono (K.filtration.step i).arrow).1
  rw [restriction_arrow]
  change (K.filtration.step i).arrow ≫ 𝟙 K.obj = _
  simp

private theorem restriction_comp {C : Type*} [Category C] [Abelian C]
    {K L M : FilteredObject C} (f : K ⟶ L) (g : L ⟶ M) (i : ℤ) :
    FilteredObject.restrictionSteps (f ≫ g) i =
      FilteredObject.restrictionSteps f i ≫ FilteredObject.restrictionSteps g i := by
  apply (cancel_mono (M.filtration.step i).arrow).1
  simp only [Category.assoc, restriction_arrow]
  rw [← Category.assoc, restriction_arrow, Category.assoc]
  rfl

private theorem graded_id {C : Type*} [Category C] [Abelian C]
    (K : FilteredObject C) (i : ℤ) :
    FilteredObject.gradedMapSteps (𝟙 K) i = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE
    (K.filtration.step (i + 1)) (K.filtration.step i)
    (K.filtration.antitone_step (by omega))))).1
  rw [graded_projection, restriction_id, Category.id_comp]
  exact (Category.comp_id _).symm

private theorem graded_comp {C : Type*} [Category C] [Abelian C]
    {K L M : FilteredObject C} (f : K ⟶ L) (g : L ⟶ M) (i : ℤ) :
    FilteredObject.gradedMapSteps (f ≫ g) i =
      FilteredObject.gradedMapSteps f i ≫ FilteredObject.gradedMapSteps g i := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE
    (K.filtration.step (i + 1)) (K.filtration.step i)
    (K.filtration.antitone_step (by omega))))).1
  calc
    _ = FilteredObject.restrictionSteps (f ≫ g) i ≫ _ := graded_projection (f ≫ g) i
    _ = (FilteredObject.restrictionSteps f i ≫
        FilteredObject.restrictionSteps g i) ≫ _ := by rw [restriction_comp]
    _ = FilteredObject.restrictionSteps f i ≫
        (FilteredObject.restrictionSteps g i ≫ _) := Category.assoc _ _ _
    _ = FilteredObject.restrictionSteps f i ≫
        (_ ≫ FilteredObject.gradedMapSteps g i) :=
      congrArg (FilteredObject.restrictionSteps f i ≫ ·) (graded_projection g i).symm
    _ = (FilteredObject.restrictionSteps f i ≫ _) ≫
        FilteredObject.gradedMapSteps g i := (Category.assoc _ _ _).symm
    _ = (_ ≫ FilteredObject.gradedMapSteps f i) ≫
        FilteredObject.gradedMapSteps g i :=
      congrArg (· ≫ FilteredObject.gradedMapSteps g i) (graded_projection f i).symm
    _ = _ := Category.assoc _ _ _

private noncomputable def gradedFunctor (R : Type u) [CommRing R] (i : ℤ) :
    FiniteFilteredModuleComplex R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj K := K.obj.filtration.gradedPiece i
  map f := FilteredObject.gradedMapSteps f.hom i
  map_id K := graded_id K.obj i
  map_comp f g := graded_comp f.hom g.hom i

private noncomputable def restrictedHomotopy {R : Type u} [CommRing R]
    {K L : FiniteFilteredModuleComplex R} {f g : K ⟶ L}
    (h : Homotopy f.hom.hom g.hom.hom)
    (hh : ∀ i n m : ℤ, ∃ lift :
      (K.obj.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X n ⟶
        (L.obj.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ).X m,
      lift ≫ (L.obj.filtration.step i).arrow.f m =
        (K.obj.filtration.step i).arrow.f n ≫ h.hom n m) (i : ℤ) :
    Homotopy (FilteredObject.restrictionSteps f.hom i)
      (FilteredObject.restrictionSteps g.hom i) := by
  classical
  choose lift hlift using hh i
  refine ⟨lift, ?_, ?_⟩
  · intro n m hnm
    apply (cancel_mono ((L.obj.filtration.step i).arrow.f m)).1
    rw [hlift, h.zero n m hnm, comp_zero, zero_comp]
  · intro n
    apply (cancel_mono ((L.obj.filtration.step i).arrow.f n)).1
    have hf := HomologicalComplex.congr_hom (restriction_arrow f.hom i) n
    have hg := HomologicalComplex.congr_hom (restriction_arrow g.hom i) n
    have hc := h.comm n
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at hc ⊢
    simp only [Preadditive.add_comp, Category.assoc, hlift]
    simp only [← (L.obj.filtration.step i).arrow.comm, ← Category.assoc, hlift]
    simp only [← (K.obj.filtration.step i).arrow.comm, Category.assoc]
    simp only [HomologicalComplex.comp_f] at hf hg
    rw [hf, hg]
    simpa only [Preadditive.comp_add, Category.assoc] using
      congrArg ((K.obj.filtration.step i).arrow.f n ≫ ·) hc

private theorem graded_homotopy {R : Type u} [CommRing R]
    (i : ℤ) (K L : FiniteFilteredModuleComplex R) (f g : K ⟶ L)
    (h : finiteFilteredModuleHomotopyRel R f g) :
    (gradedFunctor R i ⋙ DerivedCategory.Q).map f =
      (gradedFunctor R i ⋙ DerivedCategory.Q).map g := by
  classical
  change DerivedCategory.Q.map (FilteredObject.gradedMapSteps f.hom i) =
    DerivedCategory.Q.map (FilteredObject.gradedMapSteps g.hom i)
  obtain ⟨h, hh⟩ := h
  let h' := restrictedHomotopy h hh i
  let jK := Subobject.ofLE (K.obj.filtration.step (i + 1))
    (K.obj.filtration.step i) (K.obj.filtration.antitone_step (by omega))
  let jL := Subobject.ofLE (L.obj.filtration.step (i + 1))
    (L.obj.filtration.step i) (L.obj.filtration.antitone_step (by omega))
  let πK := cokernel.π jK
  let πL := cokernel.π jL
  have hres (j n m : ℤ) : (restrictedHomotopy h hh j).hom n m ≫
      (L.obj.filtration.step j).arrow.f m =
      (K.obj.filtration.step j).arrow.f n ≫ h.hom n m :=
    Classical.choose_spec (hh j n m)
  have hcompat (n m : ℤ) : jK.f n ≫ h'.hom n m =
      (restrictedHomotopy h hh (i + 1)).hom n m ≫ jL.f m := by
    apply (cancel_mono ((L.obj.filtration.step i).arrow.f m)).1
    simp only [Category.assoc, h', hres]
    rw [← Category.assoc, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
    dsimp only [jL]
    rw [← HomologicalComplex.comp_f, Subobject.ofLE_arrow, hres]
  have hz (n m : ℤ) : jK.f n ≫ h'.hom n m ≫ πL.f m = 0 := by
    rw [← Category.assoc, hcompat, Category.assoc]
    have hc := HomologicalComplex.congr_hom (cokernel.condition jL) m
    change jL.f m ≫ πL.f m = 0 at hc
    rw [hc, comp_zero]
  let lift (n m : ℤ) : (cokernel jK).X n ⟶ (cokernel jL).X m :=
    (PreservesCokernel.iso
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n) jK).hom ≫
      cokernel.desc (jK.f n) (h'.hom n m ≫ πL.f m) (hz n m)
  have hlift (n m : ℤ) : πK.f n ≫ lift n m = h'.hom n m ≫ πL.f m := by
    dsimp [lift, πK]
    have he := PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n) jK
    change (cokernel.π jK).f n ≫ _ = cokernel.π (jK.f n) at he
    rw [← Category.assoc, he, cokernel.π_desc]
  apply DerivedCategory.Q_map_eq_of_homotopy
  refine ⟨lift, ?_, ?_⟩
  · intro n m hnm
    apply (cancel_epi (πK.f n)).1
    rw [hlift, h'.zero n m hnm, zero_comp, comp_zero]
  · intro n
    apply (cancel_epi (πK.f n)).1
    have hf := HomologicalComplex.congr_hom (graded_projection f.hom i) n
    have hg := HomologicalComplex.congr_hom (graded_projection g.hom i) n
    simp only [HomologicalComplex.comp_f] at hf hg
    have hc := h'.comm n
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at hc ⊢
    simp only [Preadditive.comp_add, ← Category.assoc]
    erw [πK.comm, Category.assoc, hlift, hlift, Category.assoc, πL.comm]
    erw [hg]
    simpa only [Preadditive.add_comp, Category.assoc, πK, πL, gradedFunctor] using
      hf.trans (congrArg (· ≫ πL.f n) hc)

private noncomputable def gradedDerived (R : Type u) [CommRing R] (i : ℤ) :
    FiniteFilteredModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  CategoryTheory.Quotient.lift (finiteFilteredModuleHomotopyRel R)
    (gradedFunctor R i ⋙ DerivedCategory.Q) (graded_homotopy i)

private theorem quasiIso_iff {R : Type u} [CommRing R]
    {K L : FiniteFilteredModuleHomotopy R} (f : K ⟶ L) :
    finiteFilteredModuleQuasiIso R f ↔ ∀ i : ℤ, IsIso ((gradedDerived R i).map f) := by
  constructor
  · rintro ⟨f, rfl, hf⟩ i
    change IsIso (DerivedCategory.Q.map (FilteredObject.gradedMapSteps f.hom i))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).2 (hf i)
  · intro hf
    obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor
      (finiteFilteredModuleHomotopyRel R)).map_surjective f
    refine ⟨f, rfl, fun i ↦ ?_⟩
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).1 (hf i)

/-- Graded quasi-isomorphisms contain identities. Source: Stacks Tag 05S1:
associated grading and cohomology preserve identities.
(blueprint: lem-kun-filtered-quasi-isomorphism-fractions-two-out-of-three). -/
theorem finiteFilteredModuleQuasiIso_id (R : Type u) [CommRing R]
    (K : FiniteFilteredModuleHomotopy R) : finiteFilteredModuleQuasiIso R (𝟙 K) := by
  rw [quasiIso_iff]
  intro i
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- Graded quasi-isomorphisms have two-out-of-three. Source: Stacks Tags 05S1 and 05RM.
Restrict each filtered homotopy to filtration steps and descend it to their cokernels.
This defines graded functors on the homotopy quotient. The property is then detected by
isomorphisms under these functors to the ordinary derived category. Apply two-out-of-three
for isomorphisms in every grade.
(blueprint: lem-kun-filtered-quasi-isomorphism-fractions-two-out-of-three). -/
theorem finiteFilteredModuleQuasiIso_twoOutOfThree (R : Type u) [CommRing R] :
    (finiteFilteredModuleQuasiIso R).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := by
    rw [quasiIso_iff] at hf hg ⊢
    intro i
    have := hf i
    have := hg i
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  of_postcomp f g hg hfg := by
    rw [quasiIso_iff] at hg hfg ⊢
    intro i
    have := hg i
    have hfg := hfg i
    rw [CategoryTheory.Functor.map_comp] at hfg
    exact IsIso.of_isIso_comp_right ((gradedDerived R i).map f) ((gradedDerived R i).map g)
  of_precomp f g hf hfg := by
    rw [quasiIso_iff] at hf hfg ⊢
    intro i
    have := hf i
    have hfg := hfg i
    rw [CategoryTheory.Functor.map_comp] at hfg
    exact IsIso.of_isIso_comp_left ((gradedDerived R i).map f) ((gradedDerived R i).map g)

end CochainComplex
