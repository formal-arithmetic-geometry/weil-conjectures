/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M8
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup
import Sheaf.Algebra.Homology.FiniteFilteredGradedComparison
import all Sheaf.Algebra.Homology.FilteredQuasiIsoTwoOutOfThree

/-! # Descent of finite filtered pages and cohomology

Source: Stacks Project, Tags 012O, 012P, 05S2 and 05S3.
(blueprint: lem-kun-filtered-page-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace FilteredPageProofs

open CochainComplex

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

private theorem graded_cohomology_homotopy {R : Type u} [CommRing R]
    (i n : ℤ) (K L : FiniteFilteredModuleComplex R) (f g : K ⟶ L)
    (h : finiteFilteredModuleHomotopyRel R f g) :
    HomologicalComplex.homologyMap (FilteredObject.gradedMapSteps f.hom i) n =
      HomologicalComplex.homologyMap (FilteredObject.gradedMapSteps g.hom i) n := by
  have he := congrArg ((finiteFilteredOrdinaryH R n).map)
    (CochainComplex.graded_homotopy i K L f g h)
  apply (cancel_epi ((finiteFilteredOrdinaryHComparison R n).hom.app
    (K.obj.filtration.gradedPiece i))).1
  exact ((finiteFilteredOrdinaryHComparison R n).hom.naturality
    (FilteredObject.gradedMapSteps f.hom i)).symm.trans
      ((congrArg (· ≫ (finiteFilteredOrdinaryHComparison R n).hom.app
        (L.obj.filtration.gradedPiece i)) he).trans
          ((finiteFilteredOrdinaryHComparison R n).hom.naturality
            (FilteredObject.gradedMapSteps g.hom i)))

private theorem graded_representative (R : Type u) [CommRing R]
    {U V : FiniteFilteredModuleComplex R} (f : U ⟶ V)
    (hf : finiteFilteredModuleQuasiIso R ((finiteFilteredModuleHomotopyQuotient R).map f)) :
    ∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom a) := by
  intro a
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).1
    (((CochainComplex.quasiIso_iff _).1 hf) a)

end FilteredPageProofs

private theorem page_first_witness (R : Type u) [CommRing R]
    (U V : CochainComplex.FiniteFilteredModuleComplex R) (f : U ⟶ V) (a b : ℤ) :
    ∃ (s : ∀ i : ℤ, (U.obj.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
        (V.obj.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ))
      (g : U.obj.filtration.gradedPiece a ⟶ V.obj.filtration.gradedPiece a),
      (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
        (U.obj.filtration.step i).arrow ≫ f.hom.hom) ∧
      U.obj.filtration.complexQuotientπ a (a + 1) (Int.le_add_one le_rfl) ≫ g =
        s a ≫ V.obj.filtration.complexQuotientπ a (a + 1) (Int.le_add_one le_rfl) ∧
      (((finiteFilteredPageFunctor R).map f).hom 1).f (a, b) ≫
          (finiteFilteredPageFirstIso R V a b).hom =
        (finiteFilteredPageFirstIso R U a b).hom ≫
          HomologicalComplex.homologyMap g (a + b) := by
  have hm := (finiteFilteredPageModel R).map_spec U V f a b 1 le_rfl
  have hd := hm.choose_spec.choose_spec.choose_spec.choose_spec
  exact ⟨hm.choose, hm.choose_spec.choose_spec.choose_spec.choose,
    hd.1, hd.2.2.2.1, hd.2.2.2.2.1⟩

private theorem pageFirst_naturality (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V) (a b : ℤ) :
    (((finiteFilteredPageFunctor R).map f).hom 1).f (a, b) ≫
        (finiteFilteredPageFirstIso R V a b).hom =
      (finiteFilteredPageFirstIso R U a b).hom ≫
        HomologicalComplex.homologyMap (FilteredObject.gradedMapSteps f.hom a) (a + b) := by
  obtain ⟨s, g, hs, hg, hfirst⟩ := page_first_witness R U V f a b
  have heq (i : ℤ) : s i = FilteredObject.restrictionSteps f.hom i := by
    apply (cancel_mono (V.obj.filtration.step i).arrow).1
    exact (hs i).trans (Classical.choose_spec (f.hom.preserves i)).symm
  have hgraded : g = FilteredObject.gradedMapSteps f.hom a := by
    have : Epi (U.obj.filtration.complexQuotientπ a (a + 1) (Int.le_add_one le_rfl)) := by
      dsimp only [DecreasingFiltration.complexQuotientπ]
      infer_instance
    apply (cancel_epi (U.obj.filtration.complexQuotientπ a (a + 1) (Int.le_add_one le_rfl))).1
    rw [hg, heq]
    exact (Classical.choose_spec
      (FilteredObject.exists_gradedMap_steps U.obj V.obj f.hom a)).symm
  rw [hgraded] at hfirst
  exact hfirst

attribute [local irreducible] finiteFilteredPageFunctor finiteFilteredPageFirstIso
  finiteFilteredPageImageIso

private theorem spectral_hom_ext_first
    {C : Type v} [Category.{w} C] [Abelian C]
    {E E' : CohomologicalSpectralSequence C 1} {f g : E ⟶ E'}
    (h : f.hom 1 = g.hom 1) : f = g := by
  apply SpectralSequence.hom_ext
  intro r hr
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = 1 + k := ⟨(r - 1).toNat, by omega⟩
  induction k with
  | zero => simpa using h
  | succ k ih =>
    ext pq
    apply (cancel_epi (E.iso (1 + k) (1 + ((k + 1 : ℕ) : ℤ)) pq (by omega) (by omega)).hom).1
    exact
      (f.comm (1 + k) (1 + ((k + 1 : ℕ) : ℤ)) pq (by omega) (by omega)).symm.trans
        ((congrArg (fun m ↦ HomologicalComplex.homologyMap m pq ≫
            (E'.iso (1 + k) (1 + ((k + 1 : ℕ) : ℤ)) pq (by omega) (by omega)).hom)
          (ih (by omega))).trans
          (g.comm (1 + k) (1 + ((k + 1 : ℕ) : ℤ)) pq (by omega) (by omega)))

private theorem spectral_isIso_of_first
    {C : Type v} [Category.{w} C] [Abelian C]
    {E E' : CohomologicalSpectralSequence C 1} (f : E ⟶ E')
    (h : IsIso (f.hom 1)) : IsIso f := by
  have hall (r : ℤ) (hr : 1 ≤ r) : IsIso (f.hom r hr) := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = 1 + k := ⟨(r - 1).toNat, by omega⟩
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have hi (pq : ℤ × ℤ) : IsIso ((f.hom (1 + ((k + 1 : ℕ) : ℤ)) (by omega)).f pq) := by
        have he : (f.hom (1 + ((k + 1 : ℕ) : ℤ)) (by omega)).f pq =
            (E.iso (1 + k) (1 + ((k + 1 : ℕ) : ℤ)) pq (by omega) (by omega)).inv ≫
              HomologicalComplex.homologyMap (f.hom (1 + k) (by omega)) pq ≫
                (E'.iso (1 + k) (1 + ((k + 1 : ℕ) : ℤ)) pq (by omega) (by omega)).hom := by
          apply (cancel_epi
            (E.iso (1 + k) (1 + ((k + 1 : ℕ) : ℤ)) pq (by omega) (by omega)).hom).1
          rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
          exact (f.comm (1 + k) (1 + ((k + 1 : ℕ) : ℤ)) pq (by omega) (by omega)).symm
        have := ih (by omega)
        rw [he]
        infer_instance
      let _ : ∀ pq : ℤ × ℤ, IsIso ((f.hom (1 + ((k + 1 : ℕ) : ℤ)) (by omega)).f pq) := hi
      exact HomologicalComplex.Hom.isIso_of_components _
  let g : E' ⟶ E :=
    { hom := fun r hr ↦ inv (f.hom r hr)
      comm := fun r r' pq hrr' hr ↦ by
        have := hall r hr
        have := hall r' (by omega)
        apply (cancel_epi (HomologicalComplex.homologyMap (f.hom r hr) pq)).1
        calc
          _ = (E.iso r r' pq hrr' hr).hom := by
            rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
              IsIso.hom_inv_id, HomologicalComplex.homologyMap_id, Category.id_comp]
          _ = _ := by
            rw [← Category.assoc, f.comm r r' pq hrr' hr, Category.assoc,
              HomologicalComplex.Hom.inv_f_apply, IsIso.hom_inv_id, Category.comp_id] }
  exact ⟨⟨g, by
    apply SpectralSequence.hom_ext
    intro r hr
    have := hall r hr
    simp [g], by
    apply SpectralSequence.hom_ext
    intro r hr
    have := hall r hr
    simp [g]⟩⟩

private theorem filtered_hom_ext {C : Type v} [Category.{w} C] [Abelian C]
    {K L : FilteredObject C} {f g : K ⟶ L} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem page_homotopy (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f g : U ⟶ V)
    (h : CochainComplex.finiteFilteredModuleHomotopyRel R f g) :
    (finiteFilteredPageFunctor R).map f = (finiteFilteredPageFunctor R).map g := by
  apply spectral_hom_ext_first
  apply HomologicalComplex.Hom.ext
  funext pq
  obtain ⟨a, b⟩ := pq
  apply (cancel_mono (finiteFilteredPageFirstIso R V a b).hom).1
  rw [pageFirst_naturality, pageFirst_naturality]
  exact congrArg ((finiteFilteredPageFirstIso R U a b).hom ≫ ·)
    (FilteredPageProofs.graded_cohomology_homotopy a (a + b) U V f g h)

private theorem cohomology_homotopy (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f g : U ⟶ V)
    (h : CochainComplex.finiteFilteredModuleHomotopyRel R f g) (n : ℤ) :
    (finiteFilteredCohomology R n).map f = (finiteFilteredCohomology R n).map g := by
  apply filtered_hom_ext
  exact h.choose.homologyMap_eq n

private theorem filtered_isIso_of_restrictions
    {C : Type v} [Category.{w} C] [Abelian C]
    {K L : FilteredObject C} (f : K ⟶ L) (hf : IsIso f.hom)
    (hs : ∀ p : ℤ, IsIso (FilteredObject.restrictionSteps f p)) : IsIso f := by
  let g : L ⟶ K :=
    { hom := inv f.hom
      preserves := fun p ↦ ⟨inv (FilteredObject.restrictionSteps f p), by
        apply (cancel_mono f.hom).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [← FilteredPageProofs.restriction_arrow f p, IsIso.inv_hom_id_assoc]⟩ }
  exact ⟨⟨g, filtered_hom_ext (IsIso.hom_inv_id f.hom),
    filtered_hom_ext (IsIso.inv_hom_id f.hom)⟩⟩

private theorem filtered_graded_isIso
    {C : Type v} [Category.{w} C] [Abelian C]
    {K L : FilteredObject C} (f : K ⟶ L) (p : ℤ)
    (hs : IsIso (FilteredObject.restrictionSteps f (p + 1)))
    (ht : IsIso (FilteredObject.restrictionSteps f p)) :
    IsIso (FilteredObject.gradedMapSteps f p) := by
  let iK := Subobject.ofLE (K.filtration.step (p + 1)) (K.filtration.step p)
    (K.filtration.antitone_step (by omega))
  let iL := Subobject.ofLE (L.filtration.step (p + 1)) (L.filtration.step p)
    (L.filtration.antitone_step (by omega))
  have hw : iK ≫ FilteredObject.restrictionSteps f p =
      FilteredObject.restrictionSteps f (p + 1) ≫ iL := by
    apply (cancel_mono (L.filtration.step p).arrow).1
    dsimp only [iK, iL]
    simp only [Category.assoc, FilteredPageProofs.restriction_arrow, Subobject.ofLE_arrow]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  let e := cokernel.mapIso iK iL (asIso (FilteredObject.restrictionSteps f (p + 1)))
    (asIso (FilteredObject.restrictionSteps f p)) hw
  have he : FilteredObject.gradedMapSteps f p = e.hom := by
    apply (cancel_epi (cokernel.π iK)).1
    rw [FilteredPageProofs.graded_projection]
    simp only [e, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc, iL, asIso_hom]
  rw [he]
  infer_instance

private theorem cohomology_restriction_isIso (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V)
    (hg : ∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom a))
    (n a : ℤ) :
    IsIso (FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a) := by
  obtain ⟨hu, hs⟩ := CochainComplex.finiteFilteredModule_graded_comparison f hg
  have hstep := hs a
  let sq : Arrow.mk (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n) ⟶
      Arrow.mk (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow n) :=
    Arrow.homMk (HomologicalComplex.homologyMap (FilteredObject.restrictionSteps f.hom a) n)
      (HomologicalComplex.homologyMap f.hom.hom n) (by
        dsimp only [Arrow.mk_hom]
        rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
        congr 1
        exact Classical.choose_spec (f.hom.preserves a))
  have : IsIso sq.left := by
    change IsIso (HomologicalComplex.homologyMap (FilteredObject.restrictionSteps f.hom a) n)
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  have : IsIso sq.right := by
    change IsIso (HomologicalComplex.homologyMap f.hom.hom n)
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  have : IsIso sq := Arrow.isIso_of_isIso_left_of_isIso_right sq
  have he : FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a =
      imageSubobjectMap sq := by
    apply (cancel_mono (finiteFilteredCohomologyImage R V a n).arrow).1
    exact (Classical.choose_spec (((finiteFilteredCohomology R n).map f).preserves a)).trans
      (imageSubobjectMap_arrow sq).symm
  rw [he]
  dsimp only [imageSubobjectMap]
  have : IsIso (image.map sq) :=
    (CategoryTheory.Limits.im : Arrow (ModuleCat.{u} R) ⥤ ModuleCat.{u} R).map_isIso sq
  infer_instance

private theorem cohomology_isIso (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V)
    (hg : ∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom a)) (n : ℤ) :
    IsIso ((finiteFilteredCohomology R n).map f) := by
  have h := (CochainComplex.finiteFilteredModule_graded_comparison f hg).1
  apply filtered_isIso_of_restrictions
  · exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap f.hom.hom n))
  · exact cohomology_restriction_isIso R f hg n

private theorem page_isIso (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V)
    (hg : ∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom a)) :
    IsIso ((finiteFilteredPageFunctor R).map f) := by
  apply spectral_isIso_of_first
  have hi (pq : ℤ × ℤ) : IsIso ((((finiteFilteredPageFunctor R).map f).hom 1).f pq) := by
    obtain ⟨a, b⟩ := pq
    have h := hg a
    have he : (((finiteFilteredPageFunctor R).map f).hom 1).f (a, b) =
        (finiteFilteredPageFirstIso R U a b).hom ≫
          HomologicalComplex.homologyMap (FilteredObject.gradedMapSteps f.hom a) (a + b) ≫
            (finiteFilteredPageFirstIso R V a b).inv := by
      apply (cancel_mono (finiteFilteredPageFirstIso R V a b).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact pageFirst_naturality R f a b
    rw [he]
    infer_instance
  let _ : ∀ pq : ℤ × ℤ, IsIso ((((finiteFilteredPageFunctor R).map f).hom 1).f pq) := hi
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem descend_functor (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C] (F : CochainComplex.FiniteFilteredModuleComplex R ⥤ C)
    (hh : ∀ (U V : CochainComplex.FiniteFilteredModuleComplex R) (f g : U ⟶ V),
      CochainComplex.finiteFilteredModuleHomotopyRel R f g → F.map f = F.map g)
    (hw : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V),
      (∀ a : ℤ, QuasiIso (FilteredObject.gradedMapSteps f.hom a)) → IsIso (F.map f)) :
    ∃ Fbar : finiteFilteredModuleDerivedCategory R ⥤ C,
      Nonempty (finiteFilteredDerivedQuotient R ⋙ Fbar ≅ F) := by
  let P := CategoryTheory.Quotient.lift (CochainComplex.finiteFilteredModuleHomotopyRel R) F hh
  have hP : (CochainComplex.finiteFilteredModuleQuasiIso R).IsInvertedBy P := by
    rintro U V w ⟨f, rfl, hf⟩
    exact hw f hf
  exact ⟨Localization.lift P hP (finiteFilteredModuleLocalizationFunctor R),
    ⟨Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (CochainComplex.finiteFilteredModuleHomotopyQuotient R)
        (Localization.fac P hP (finiteFilteredModuleLocalizationFunctor R)) ≪≫
      CategoryTheory.Quotient.lift.isLift _ F hh⟩⟩

private theorem descend_iso (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C]
    (F G : finiteFilteredModuleDerivedCategory R ⥤ C)
    (e : finiteFilteredDerivedQuotient R ⋙ F ≅ finiteFilteredDerivedQuotient R ⋙ G) :
    ∃ ebar : F ≅ G, ∀ U : CochainComplex.FiniteFilteredModuleComplex R,
      ebar.hom.app ((finiteFilteredDerivedQuotient R).obj U) = e.hom.app U := by
  let q := CochainComplex.finiteFilteredModuleHomotopyQuotient R
  let L := finiteFilteredModuleLocalizationFunctor R
  let W := CochainComplex.finiteFilteredModuleQuasiIso R
  have := Localization.full_whiskeringLeft L W C
  have := Localization.faithful_whiskeringLeft L W C
  let T := (Functor.whiskeringLeft _ _ C).obj L ⋙
    (Functor.whiskeringLeft _ _ C).obj q
  have : T.Full := by
    dsimp only [T, q, CochainComplex.finiteFilteredModuleHomotopyQuotient]
    infer_instance
  have : T.Faithful := by
    dsimp only [T, q, CochainComplex.finiteFilteredModuleHomotopyQuotient]
    infer_instance
  let e' : T.obj F ≅ T.obj G :=
    (Functor.associator q L F).symm ≪≫ e ≪≫ Functor.associator q L G
  refine ⟨T.preimageIso e', ?_⟩
  intro U
  have he := congrArg (fun τ ↦ τ.app U) (T.map_preimage e'.hom)
  change (T.preimage e'.hom).app ((finiteFilteredDerivedQuotient R).obj U) =
    e'.hom.app U at he
  have he' : e'.hom.app U = e.hom.app U := by
    change 𝟙 _ ≫ (e.hom.app U ≫ 𝟙 _) = e.hom.app U
    exact (Category.id_comp _).trans (Category.comp_id _)
  exact he.trans he'

private theorem descend_naturality (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C]
    (F G : CochainComplex.FiniteFilteredModuleComplex R ⥤ C)
    (Fbar Gbar : finiteFilteredModuleDerivedCategory R ⥤ C)
    (eF : finiteFilteredDerivedQuotient R ⋙ Fbar ≅ F)
    (eG : finiteFilteredDerivedQuotient R ⋙ Gbar ≅ G) (e : F ≅ G)
    {U V : CochainComplex.FiniteFilteredModuleComplex R}
    (α : (finiteFilteredDerivedQuotient R).obj U ⟶
      (finiteFilteredDerivedQuotient R).obj V) :
    finiteFilteredDescendedMap R F Fbar eF α ≫ e.hom.app V =
      e.hom.app U ≫ finiteFilteredDescendedMap R G Gbar eG α := by
  obtain ⟨τ, hτ⟩ := descend_iso R Fbar Gbar (eF ≪≫ e ≪≫ eG.symm)
  have h := τ.hom.naturality α
  rw [hτ U, hτ V] at h
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at h
  apply (cancel_epi (eF.hom.app U)).1
  apply (cancel_mono (eG.inv.app V)).1
  dsimp only [finiteFilteredDescendedMap]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simpa only [Category.assoc, Category.comp_id, Category.id_comp] using h

/-- Pages and image-filtered cohomology factor through filtered localization.
Source: Stacks Project, Tags 012O, 012P, 05S2 and 05S3.
(blueprint: lem-kun-filtered-page-descent).

Proof. Filtered homotopies restrict to the filtration steps and descend to their
cokernels; they therefore induce equal maps on graded cohomology. The normalized
first-page comparison and induction through successor homology give equality on
all pages. Graded comparison for finite filtrations shows that a graded
quasi-isomorphism is a quasi-isomorphism on every step and on the whole complex.
Its cohomology maps restrict to isomorphisms on the image filtration, and the
first-page comparison and successor induction make its page map an isomorphism.
Apply the quotient and localization universal properties to the page, cohomology,
underlying-derived and graded-derived functors. Lift the ordinary cohomology and
first-page natural comparisons by full faithfulness of precomposition. Their
normalization equations follow on chain representatives and then on the
localization by uniqueness. -/
theorem filteredPageDescent (R : Type u) [CommRing R] :
    Nonempty (FilteredPageDescentData R) := by
  classical
  obtain ⟨Sbar, ⟨eS⟩⟩ := descend_functor R (finiteFilteredPageFunctor R)
    (fun U V f g h ↦ page_homotopy R f g h) (page_isIso R)
  have hH (n : ℤ) := descend_functor R (finiteFilteredCohomology R n)
    (fun U V f g h ↦ cohomology_homotopy R f g h n)
    (fun f hf ↦ cohomology_isIso R f hf n)
  choose Hbar heH using hH
  let eH (n : ℤ) := (heH n).some
  obtain ⟨omega, ⟨eOmega⟩⟩ := descend_functor R
    (finiteFilteredComplexForget R ⋙ finiteFilteredOrdinaryQ R)
    (fun U V f g h ↦ DerivedCategory.Q_map_eq_of_homotopy (ModuleCat R) h.choose)
    (fun f hf ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).2
      (CochainComplex.finiteFilteredModule_graded_comparison f hf).1)
  have hG (a : ℤ) := descend_functor R
    (FilteredPageProofs.gradedFunctor R a ⋙ finiteFilteredOrdinaryQ R)
    (fun U V f g h ↦ CochainComplex.graded_homotopy a U V f g h)
    (fun f hf ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).2 (hf a))
  choose gradedDerived heG using hG
  let eG (a : ℤ) := (heG a).some
  have hOrd (n : ℤ) : ∃ e : Hbar n ⋙ finiteFilteredCohomologyForget R ≅
      omega ⋙ finiteFilteredOrdinaryH R n,
      ∀ U : CochainComplex.FiniteFilteredModuleComplex R,
      e.hom.app ((finiteFilteredDerivedQuotient R).obj U) ≫
          (finiteFilteredOrdinaryH R n).map (eOmega.hom.app U) ≫
          (finiteFilteredOrdinaryHComparison R n).hom.app U.obj.obj =
        ((eH n).hom.app U).hom := by
    let A := (Functor.associator (finiteFilteredDerivedQuotient R) (Hbar n)
        (finiteFilteredCohomologyForget R)).symm ≪≫
      isoWhiskerRight (eH n) (finiteFilteredCohomologyForget R)
    let B := (Functor.associator (finiteFilteredDerivedQuotient R) omega
        (finiteFilteredOrdinaryH R n)).symm ≪≫
      isoWhiskerRight eOmega (finiteFilteredOrdinaryH R n) ≪≫
      Functor.associator (finiteFilteredComplexForget R) (finiteFilteredOrdinaryQ R)
        (finiteFilteredOrdinaryH R n) ≪≫
      isoWhiskerLeft (finiteFilteredComplexForget R) (finiteFilteredOrdinaryHComparison R n)
    obtain ⟨e, he⟩ := descend_iso R _ _ (A ≪≫ B.symm)
    refine ⟨e, ?_⟩
    intro U
    rw [he U]
    simp only [A, B, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerRight_inv, isoWhiskerLeft_inv,
      whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp only [Functor.map_id, Category.id_comp]
    change ((eH n).hom.app U).hom ≫
      (finiteFilteredOrdinaryHComparison R n).inv.app U.obj.obj ≫
      (finiteFilteredOrdinaryHComparison R n).hom.app U.obj.obj = _
    rw [Iso.inv_hom_id_app]
    exact Category.comp_id _
  choose ordinaryCohomology hordinary using hOrd
  refine ⟨{
    Sbar := Sbar
    eS := eS
    Hbar := Hbar
    eH := eH
    omega := omega
    eOmega := eOmega
    ordinaryCohomology := ordinaryCohomology
    ordinary_normalization := fun U n ↦ hordinary n U
    gradedDerived := gradedDerived
    gradedComparison := fun U a ↦ (eG a).app U
    graded_chain := fun f a ↦ (eG a).hom.naturality f
    page_one := ?_
    page_one_chain := pageFirst_naturality R
    homotopy_invariance := ?_
    quasiIso_representatives := ?_
    quasiIso_pages := ?_
  }⟩
  · intro U V α a b
    let P := SpectralSequence.pageFunctor (ModuleCat.{u} R)
      (fun r ↦ ComplexShape.up' (r, 1 - r)) 1 1 le_rfl ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up' (1, 0)) (a, b)
    let F := finiteFilteredPageFunctor R ⋙ P
    let G := FilteredPageProofs.gradedFunctor R a ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) (a + b)
    let eF : finiteFilteredDerivedQuotient R ⋙ (Sbar ⋙ P) ≅ F :=
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight eS P
    let eGr : finiteFilteredDerivedQuotient R ⋙
        (gradedDerived a ⋙ finiteFilteredOrdinaryH R (a + b)) ≅ G :=
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (eG a) (finiteFilteredOrdinaryH R (a + b)) ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft (FilteredPageProofs.gradedFunctor R a)
          (finiteFilteredOrdinaryHComparison R (a + b))
    let eFirst : F ≅ G := NatIso.ofComponents
      (fun U ↦ finiteFilteredPageFirstIso R U a b)
      (fun f ↦ pageFirst_naturality R f a b)
    have h := descend_naturality R F G (Sbar ⋙ P)
      (gradedDerived a ⋙ finiteFilteredOrdinaryH R (a + b)) eF eGr eFirst α
    simpa only [finiteFilteredDescendedMap, F, G, P, eF, eGr, eFirst,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerRight_inv, isoWhiskerLeft_hom, isoWhiskerLeft_inv,
      whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, NatIso.ofComponents_hom_app, Functor.comp_map,
      Iso.app_hom, Iso.app_inv, FilteredPageProofs.gradedFunctor,
      SpectralSequence.pageFunctor_map, HomologicalComplex.eval_map,
      SpectralSequence.comp_hom, HomologicalComplex.comp_f, Functor.map_comp,
      Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc] using h
  · intro U V f g h
    refine ⟨page_homotopy R f g h, ?_⟩
    intro n
    have heq := cohomology_homotopy R f g h n
    exact ⟨h.choose.homologyMap_eq n, heq, fun a ↦
      ⟨congrArg (fun f ↦ FilteredObject.restrictionSteps f a) heq,
        congrArg (fun f ↦ FilteredObject.gradedMapSteps f a) heq⟩⟩
  · intro U V f hf
    have hg := FilteredPageProofs.graded_representative R f hf
    obtain ⟨hu, hs⟩ := CochainComplex.finiteFilteredModule_graded_comparison f hg
    refine ⟨hu, hs, fun n ↦ ⟨?_, cohomology_isIso R f hg n, fun a ↦ ⟨?_, ?_⟩⟩⟩
    · infer_instance
    · exact cohomology_restriction_isIso R f hg n a
    · exact filtered_graded_isIso _ a
        (cohomology_restriction_isIso R f hg n (a + 1))
        (cohomology_restriction_isIso R f hg n a)
  · intro K L w hw
    have : IsIso ((finiteFilteredModuleLocalizationFunctor R).map w) :=
      (CochainComplex.finiteFilteredModuleQuasiIso R).Q_inverts w hw
    have : IsIso (Sbar.map ((finiteFilteredModuleLocalizationFunctor R).map w)) :=
      inferInstance
    refine ⟨inferInstance, fun t ht ↦ ?_⟩
    exact inferInstanceAs (IsIso ((SpectralSequence.pageFunctor (ModuleCat R) _ 1 t ht).map
      (Sbar.map ((finiteFilteredModuleLocalizationFunctor R).map w))))

end CategoryTheory
