/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M8
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup
import all WeilConjectures.CategoryTheory.FilteredStationaryCycleComparison
import all Sheaf.Algebra.Homology.FilteredPageDescent
import Sheaf.Algebra.Homology.StationaryLocalizationNaturality

/-! # Stationary comparison for finite filtered pages

Source: Stacks Project, Tags 012O, 012P, 05S2 and 05S3.
(blueprint: lem-kun-filtered-page-stationary).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_image_graded (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a n : ℤ) :
    ∃ e : finiteFilteredQuotientImage R U a n ≅
        (finiteFilteredCohomologyFiltration R U n).gradedPiece a,
      factorThruImage (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) n) ≫
          e.hom =
        factorThruImageSubobject
            (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n) ≫
          cokernel.π (Subobject.ofLE _ _
            ((finiteFilteredCohomologyFiltration R U n).F_succ_le a)) := by
  let S := ShortComplex.cokernelSequence (U.obj.filtration.step (a + 1)).arrow
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := by dsimp [S, ShortComplex.cokernelSequence]; infer_instance }
  have he := hS.homology_exact₂ n
  have hk : kernelSubobject (HomologicalComplex.homologyMap
        (cokernel.π (U.obj.filtration.step (a + 1)).arrow) n) =
      finiteFilteredCohomologyImage R U (a + 1) n :=
    ((ShortComplex.exact_iff_image_eq_kernel _).1 he).symm
  let f := factorThruImage
    (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) n)
  let g := factorThruImageSubobject
      (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n) ≫
    cokernel.π (Subobject.ofLE _ _
      ((finiteFilteredCohomologyFiltration R U n).F_succ_le a))
  have hf : Epi f := by dsimp [f]; infer_instance
  have hg : Epi g := by dsimp [g]; infer_instance
  have hker : kernelSubobject f = kernelSubobject g := by
    calc
      _ = kernelSubobject (f ≫ image.ι
          (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) n)) :=
        (kernelSubobject_comp_mono _ _).symm
      _ = kernelSubobject
          (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) n) :=
        congrArg (fun q ↦ kernelSubobject q) (image.fac _)
      _ = (Subobject.pullback
          (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n)).obj
          (finiteFilteredCohomologyImage R U (a + 1) n) := by
        have hm : HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) n =
            HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n ≫
              HomologicalComplex.homologyMap
                (cokernel.π (U.obj.filtration.step (a + 1)).arrow) n :=
          HomologicalComplex.homologyMap_comp _ _ n
        exact (congrArg (fun k ↦ kernelSubobject k) hm).trans
          ((BigradedExactCouple.pullback_kernelSubobject _ _).symm.trans
            (congrArg (fun Z ↦ (Subobject.pullback
              (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n)).obj Z) hk))
      _ = kernelSubobject g := by
        simpa only [g, finiteFilteredCohomologyFiltration, finiteFilteredCohomologyImage,
          DecreasingFiltration.step, imageSubobject_arrow_comp] using
          (quotient_kernel
            ((finiteFilteredCohomologyFiltration R U n).step (a + 1))
            ((finiteFilteredCohomologyFiltration R U n).step a)
            ((finiteFilteredCohomologyFiltration R U n).F_succ_le a)
            (factorThruImageSubobject
              (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n))).symm
  exact epi_iso_of_kernel_eq f g hker

private noncomputable def pageQuotientIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t) :
    (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) ≅
      filteredComplexPageObject U.obj.obj U.obj.filtration t (a, b) :=
  (finiteFilteredPageModel R).eZ U a b t ht

private theorem transition_to_ambient (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a t : ℤ) (ht : 1 ≤ t) :
    U.obj.filtration.complexQuotientπ a (a + t) (by omega) ≫
        finiteFilteredPageTransition R U a t ht ≫
        finiteFilteredWindowToAmbient R U a t ht = finiteFilteredAmbientMap R U a := by
  rw [← Category.assoc, finiteFilteredPageTransition_projection]
  dsimp only [finiteFilteredWindowToAmbient, DecreasingFiltration.complexQuotientπ,
    finiteFilteredAmbientMap, finiteFilteredAmbientQuotient]
  rw [Category.assoc, cokernel.π_desc, ← Category.assoc, Subobject.ofLE_arrow]

private theorem page_representatives (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t) :
    ∃ (z : (U.obj.filtration.complexCycleRepresentatives a (a + b) t : ModuleCat.{u} R) ⟶
        (U.obj.filtration.complexCycles a (a + b) t : ModuleCat.{u} R))
      (g : (U.obj.filtration.complexCycleRepresentatives a (a + b) t : ModuleCat.{u} R) ⟶
        (U.obj.filtration.complexQuotient a (a + t) (by omega)).cycles (a + b)),
      z ≫ (U.obj.filtration.complexCycles a (a + b) t).arrow =
        (U.obj.filtration.complexCycleRepresentatives a (a + b) t).arrow ≫
          (U.obj.filtration.complexQuotientπ a (a + 1) (by omega)).f (a + b) ∧
      g ≫ (U.obj.filtration.complexQuotient a (a + t) (by omega)).iCycles (a + b) =
        (U.obj.filtration.complexCycleRepresentatives a (a + b) t).arrow ≫
          (U.obj.filtration.complexQuotientπ a (a + t) (by omega)).f (a + b) ∧
      z ≫ filteredComplexPageπ U.obj.obj U.obj.filtration t (a, b) ≫
          (pageQuotientIso R U a b t ht).inv ≫
          (finiteFilteredPageImageIso R U a b t ht).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (finiteFilteredPageTransition R U a t ht) (a + b)) =
        g ≫ (U.obj.filtration.complexQuotient a (a + t) (by omega)).homologyπ (a + b) ≫
          HomologicalComplex.homologyMap (finiteFilteredPageTransition R U a t ht) (a + b) := by
  exact (finiteFilteredPageModel R).representative_spec U a b t ht


private theorem page_actual_cycles_core (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t)
    (z : (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).cycles (a + b) ⟶
      (U.obj.filtration.complexCycles a (a + b) t : ModuleCat.{u} R))
    (hz : z ≫ (U.obj.filtration.complexCycles a (a + b) t).arrow =
      (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).iCycles (a + b) ≫
        (U.obj.filtration.complexQuotientπ a (a + 1) (Int.le_add_one le_rfl)).f (a + b)) :
    z ≫ filteredComplexPageπ U.obj.obj U.obj.filtration t (a, b) ≫
        (pageQuotientIso R U a b t ht).inv ≫
        (finiteFilteredPageImageIso R U a b t ht).hom ≫
        image.ι (HomologicalComplex.homologyMap (finiteFilteredPageTransition R U a t ht)
          (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredWindowToAmbient R U a t ht) (a + b) =
      (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).homologyπ (a + b) ≫
        HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b) := by
  have hat : a ≤ a + t := by omega
  obtain ⟨z', g, hz', hg, hnorm⟩ := page_representatives R U a b t ht
  let F := U.obj.filtration
  let L : CochainComplex (ModuleCat.{u} R) ℤ := F.step a
  let T := F.complexCycleRepresentatives a (a + b) t
  have hT : T.Factors (L.iCycles (a + b)) := by
    dsimp only [T, DecreasingFiltration.complexCycleRepresentatives]
    apply (pullback_factors_iff _ _ _).2
    apply (Subobject.inf_factors _).2
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).2
      have hd : L.iCycles (a + b) ≫ (F.step a).arrow.f (a + b) ≫
          U.obj.obj.d (a + b) (a + b + 1) = 0 := by
        rw [(F.step a).arrow.comm, ← Category.assoc, HomologicalComplex.iCycles_d,
          zero_comp]
      rw [Category.assoc, hd]
      exact Subobject.factors_zero
  let c := T.factorThru (L.iCycles (a + b)) hT
  have hc : c ≫ T.arrow = L.iCycles (a + b) := Subobject.factorThru_arrow _ _ _
  have hcz : c ≫ z' = z := by
    apply (cancel_mono (F.complexCycles a (a + b) t).arrow).1
    rw [Category.assoc, hz', ← Category.assoc, hc]
    exact hz.symm
  have hcg : c ≫ g = HomologicalComplex.cyclesMap
      (F.complexQuotientπ a (a + t) hat) (a + b) := by
    apply (cancel_mono ((F.complexQuotient a (a + t) hat).iCycles (a + b))).1
    rw [Category.assoc, hg, ← Category.assoc, hc, HomologicalComplex.cyclesMap_i]
  have h := congrArg (fun f ↦ c ≫ f ≫ HomologicalComplex.homologyMap
    (finiteFilteredWindowToAmbient R U a t ht) (a + b)) hnorm
  simp only [← Category.assoc, hcz, hcg] at h
  calc
    _ = (HomologicalComplex.cyclesMap
          (F.complexQuotientπ a (a + t) hat) (a + b) ≫
        (F.complexQuotient a (a + t) hat).homologyπ (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredPageTransition R U a t ht) (a + b) ≫
        HomologicalComplex.homologyMap (finiteFilteredWindowToAmbient R U a t ht) (a + b) := by
      simpa only [Category.assoc, pageQuotientIso, finiteFilteredPageImageIso,
        filteredComplexPageπ] using h
    _ = _ := by
      rw [← HomologicalComplex.homologyπ_naturality]
      simp only [Category.assoc, ← HomologicalComplex.homologyMap_comp]
      rw [transition_to_ambient]

private theorem complexStep_bot {C : Type v} [Category.{w} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (i n : ℤ)
    (h : F.step i = ⊥) : F.complexStep i n = ⊥ := by
  have hz : IsZero (F.step i : CochainComplex C ℤ) := by
    rw [h]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  have hn := (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_isZero hz
  dsimp only [DecreasingFiltration.complexStep]
  simpa only [hn.eq_zero_of_src ((F.step i).arrow.f n)] using
    (imageSubobject_zero (A := (F.step i : CochainComplex C ℤ).X n) (B := K.X n))

private theorem complexStep_top {C : Type v} [Category.{w} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (i n : ℤ)
    (h : F.step i = ⊤) : F.complexStep i n = ⊤ := by
  have : IsIso (F.step i).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  have : IsIso ((F.step i).arrow.f n) :=
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_isIso (F.step i).arrow
  dsimp only [DecreasingFiltration.complexStep]
  rw [imageSubobject_mono]
  exact Subobject.mk_eq_top_of_isIso _

set_option backward.isDefEq.respectTransparency false in
private theorem stationary_comparison (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t)
    (hu : U.obj.filtration.step (a + t) = ⊥)
    (hl : U.obj.filtration.step (a - t + 1) = ⊤) :
    Nonempty (FilteredPageStationaryComparison R U a b t ht) := by
  obtain ⟨z, e0, hzepi, hz, he0⟩ := filteredStationary_cycle_comparison
    U.obj.obj U.obj.filtration a b t ht
    (complexStep_bot U.obj.filtration (a + t) (a + b + 1) hu)
    (complexStep_top U.obj.filtration (a - t + 1) (a + b - 1) hl)
    (Iso.refl _) (finiteFilteredCohomologyFiltration R U (a + b))
    (fun i ↦ factorThruImageSubobject
      (HomologicalComplex.homologyMap (U.obj.filtration.step i).arrow (a + b)))
    (fun i ↦ by
      change _ ≫ (imageSubobject _).arrow = _ ≫ (Iso.refl _).hom
      rw [imageSubobject_arrow_comp, Iso.refl_hom, Category.comp_id])
    (fun i ↦ by infer_instance)
  have : Epi z := hzepi
  let e := pageQuotientIso R U a b t ht ≪≫ e0
  have he : z ≫ filteredComplexPageπ U.obj.obj U.obj.filtration t (a, b) ≫
        (pageQuotientIso R U a b t ht).inv ≫ e.hom =
      (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).homologyπ (a + b) ≫
        factorThruImageSubobject
          (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a)) := by
    simpa only [e, Iso.trans_hom, Iso.inv_hom_id_assoc] using he0
  obtain ⟨eQ, hforward⟩ := quotient_image_graded R U a (a + b)
  have hinverse : factorThruImageSubobject
          (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a)) ≫ eQ.inv =
      factorThruImage
        (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) := by
    rw [← Category.assoc, ← hforward, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨{
    pageToImage := e ≪≫ eQ.symm
    imageToGraded := eQ
    representative_forward := hforward
    representative_inverse := hinverse
    core_normalization := ?_
  }⟩
  have : Epi (filteredComplexPageπ U.obj.obj U.obj.filtration t (a, b)) := by
    dsimp only [filteredComplexPageπ]
    infer_instance
  let p := z ≫ filteredComplexPageπ U.obj.obj U.obj.filtration t (a, b) ≫
    (pageQuotientIso R U a b t ht).inv
  have : Epi p := by dsimp only [p]; infer_instance
  apply (cancel_epi p).1
  change p ≫ (e.hom ≫ eQ.inv) ≫ _ = _
  let h := (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).homologyπ (a + b)
  let j := factorThruImageSubobject
    (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow (a + b))
  let q := cokernel.π (Subobject.ofLE _ _
    ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a))
  let m := HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)
  have hp : p ≫ e.hom = h ≫ j ≫ q := he
  have hi : j ≫ q ≫ eQ.inv = factorThruImage m := hinverse
  calc
    p ≫ (e.hom ≫ eQ.inv) ≫ image.ι m =
        (p ≫ e.hom) ≫ eQ.inv ≫ image.ι m := by simp only [Category.assoc]
    _ = h ≫ j ≫ q ≫ eQ.inv ≫ image.ι m := by
      simpa only [Category.assoc] using congrArg (· ≫ eQ.inv ≫ image.ι m) hp
    _ = h ≫ (j ≫ q ≫ eQ.inv) ≫ image.ι m := by simp only [Category.assoc]
    _ = h ≫ factorThruImage m ≫ image.ι m := by rw [hi]
    _ = h ≫ m := by rw [image.fac]
    _ = _ := (page_actual_cycles_core R U a b t ht z hz).symm

private theorem ambient_square (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V) (a : ℤ) :
    FilteredObject.restrictionSteps f.hom a ≫ finiteFilteredAmbientMap R V a =
      finiteFilteredAmbientMap R U a ≫ finiteFilteredAmbientQuotientMap R f a := by
  dsimp only [finiteFilteredAmbientMap, finiteFilteredAmbientQuotientMap, cokernel.map]
  rw [← Category.assoc, FilteredPageProofs.restriction_arrow, Category.assoc,
    Category.assoc, cokernel.π_desc]

private theorem image_restriction_square (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V) (a n : ℤ) :
    factorThruImageSubobject
        (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n) ≫
        FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a =
      HomologicalComplex.homologyMap (FilteredObject.restrictionSteps f.hom a) n ≫
        factorThruImageSubobject
          (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow n) := by
  have hi : FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a ≫
      (imageSubobject (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow n)).arrow =
      (imageSubobject (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n)).arrow ≫
        HomologicalComplex.homologyMap f.hom.hom n :=
    FilteredPageProofs.restriction_arrow ((finiteFilteredCohomology R n).map f) a
  apply (cancel_mono (imageSubobject
    (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow n)).arrow).1
  simp only [Category.assoc, hi, imageSubobject_arrow_comp]
  simp only [← Category.assoc, imageSubobject_arrow_comp,
    ← HomologicalComplex.homologyMap_comp, FilteredPageProofs.restriction_arrow]

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_image_chain (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V) (a b : ℤ)
    (eU : finiteFilteredQuotientImage R U a (a + b) ≅
      (finiteFilteredCohomologyFiltration R U (a + b)).gradedPiece a)
    (eV : finiteFilteredQuotientImage R V a (a + b) ≅
      (finiteFilteredCohomologyFiltration R V (a + b)).gradedPiece a)
    (hU : factorThruImage
        (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) ≫ eU.hom =
      factorThruImageSubobject
          (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a)))
    (hV : factorThruImage
        (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R V a) (a + b)) ≫ eV.hom =
      factorThruImageSubobject
          (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R V (a + b)).F_succ_le a))) :
    eU.hom ≫ FilteredObject.gradedMapSteps ((finiteFilteredCohomology R (a + b)).map f) a ≫
        eV.inv ≫ image.ι
          (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R V a) (a + b)) =
      image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredAmbientQuotientMap R f a) (a + b) := by
  apply (cancel_epi (factorThruImage
    (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)))).1
  simp only [← Category.assoc]
  rw [hU]
  simp only [Category.assoc]
  have hp : cokernel.π (Subobject.ofLE _ _
        ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a)) ≫
        FilteredObject.gradedMapSteps ((finiteFilteredCohomology R (a + b)).map f) a =
      FilteredObject.restrictionSteps ((finiteFilteredCohomology R (a + b)).map f) a ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R V (a + b)).F_succ_le a)) :=
    FilteredPageProofs.graded_projection ((finiteFilteredCohomology R (a + b)).map f) a
  rw [reassoc_of% hp]
  rw [← Category.assoc, image_restriction_square]
  have hVi := congrArg (· ≫ eV.inv) hV
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hVi
  simp only [Category.assoc]
  rw [reassoc_of% hVi.symm, image.fac]
  simp only [← HomologicalComplex.homologyMap_comp, ← Category.assoc, image.fac]
  exact congrArg (fun k ↦ HomologicalComplex.homologyMap k (a + b)) (ambient_square R f a)

private theorem page_image_witness (R : Type u) [CommRing R]
    (U V : CochainComplex.FiniteFilteredModuleComplex R) (f : U ⟶ V)
    (a b t : ℤ) (ht : 1 ≤ t) :
    ∃ (s : ∀ i : ℤ, (U.obj.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
        (V.obj.filtration.step i : CochainComplex (ModuleCat.{u} R) ℤ))
      (β : U.obj.filtration.complexQuotient (a - t + 1) (a + 1) (by omega) ⟶
        V.obj.filtration.complexQuotient (a - t + 1) (a + 1) (by omega)),
      (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
        (U.obj.filtration.step i).arrow ≫ f.hom.hom) ∧
      U.obj.filtration.complexQuotientπ (a - t + 1) (a + 1) (by omega) ≫ β =
        s (a - t + 1) ≫
          V.obj.filtration.complexQuotientπ (a - t + 1) (a + 1) (by omega) ∧
      (((finiteFilteredPageFunctor R).map f).hom t ht).f (a, b) ≫
          (finiteFilteredPageImageIso R V a b t ht).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (finiteFilteredPageTransition R V a t ht) (a + b)) =
        (finiteFilteredPageImageIso R U a b t ht).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (finiteFilteredPageTransition R U a t ht) (a + b)) ≫
          HomologicalComplex.homologyMap β (a + b) := by
  have hm := (finiteFilteredPageModel R).map_spec U V f a b t ht
  have hd := hm.choose_spec.choose_spec.choose_spec.choose_spec
  exact ⟨hm.choose, hm.choose_spec.choose_spec.choose,
    hd.1, hd.2.2.1, hd.2.2.2.2.2⟩

private theorem comparison_chain (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V)
    (a b t : ℤ) (ht : 1 ≤ t)
    (cU : FilteredPageStationaryComparison R U a b t ht)
    (cV : FilteredPageStationaryComparison R V a b t ht) :
    (((finiteFilteredPageFunctor R).map f).hom t ht).f (a, b) ≫ cV.pageToImage.hom =
      cU.pageToImage.hom ≫ cU.imageToGraded.hom ≫
        FilteredObject.gradedMapSteps ((finiteFilteredCohomology R (a + b)).map f) a ≫
          cV.imageToGraded.inv := by
  obtain ⟨s, β, hs, hβ, hpage⟩ := page_image_witness R U V f a b t ht
  have hwindow : β ≫ finiteFilteredWindowToAmbient R V a t ht =
      finiteFilteredWindowToAmbient R U a t ht ≫
        finiteFilteredAmbientQuotientMap R f a := by
    have hle : a - t + 1 ≤ a + 1 := by omega
    have : Epi (U.obj.filtration.complexQuotientπ (a - t + 1) (a + 1) hle) := by
      dsimp only [DecreasingFiltration.complexQuotientπ]
      infer_instance
    apply (cancel_epi
      (U.obj.filtration.complexQuotientπ (a - t + 1) (a + 1) hle)).1
    rw [← Category.assoc, hβ]
    dsimp only [finiteFilteredWindowToAmbient, DecreasingFiltration.complexQuotientπ,
      finiteFilteredAmbientQuotientMap, cokernel.map]
    simp only [Category.assoc, cokernel.π_desc_assoc, cokernel.π_desc]
    rw [← Category.assoc, hs]
    simp only [Category.assoc]
  apply (cancel_mono (image.ι
    (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R V a) (a + b)))).1
  calc
    _ = (((finiteFilteredPageFunctor R).map f).hom t ht).f (a, b) ≫
        (finiteFilteredPageImageIso R V a b t ht).hom ≫
        image.ι (HomologicalComplex.homologyMap
          (finiteFilteredPageTransition R V a t ht) (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredWindowToAmbient R V a t ht) (a + b) := by
      simp only [Category.assoc, cV.core_normalization]
    _ = (finiteFilteredPageImageIso R U a b t ht).hom ≫
        image.ι (HomologicalComplex.homologyMap
          (finiteFilteredPageTransition R U a t ht) (a + b)) ≫
        HomologicalComplex.homologyMap β (a + b) ≫
        HomologicalComplex.homologyMap (finiteFilteredWindowToAmbient R V a t ht) (a + b) := by
      simpa only [Category.assoc] using congrArg (· ≫
        HomologicalComplex.homologyMap (finiteFilteredWindowToAmbient R V a t ht)
          (a + b)) hpage
    _ = cU.pageToImage.hom ≫ image.ι
        (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredAmbientQuotientMap R f a) (a + b) := by
      rw [← HomologicalComplex.homologyMap_comp, hwindow,
        HomologicalComplex.homologyMap_comp]
      simpa only [Category.assoc] using congrArg (· ≫
        HomologicalComplex.homologyMap (finiteFilteredAmbientQuotientMap R f a) (a + b))
        cU.core_normalization.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg (cU.pageToImage.hom ≫ ·)
        (quotient_image_chain R f a b cU.imageToGraded cV.imageToGraded
          cU.representative_forward cV.representative_forward).symm

private theorem stationary_bound_exists (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :
    ∃ B : ℤ, 1 ≤ B ∧ ∀ (t : ℤ) (ht : 1 ≤ t), B ≤ t →
      U.obj.filtration.step (a + t) = ⊥ ∧
      U.obj.filtration.step (a - t + 1) = ⊤ ∧
      (((finiteFilteredPageFunctor R).obj U).page t ht).d
          (a, b) (a + t, b - t + 1) = 0 ∧
      (((finiteFilteredPageFunctor R).obj U).page t ht).d
          (a - t, b + t - 1) (a, b) = 0 := by
  obtain ⟨lo, hi, hlo, hhi⟩ := U.property
  obtain ⟨B, hB, hb⟩ := (finiteFilteredPageModel R).stabilize_spec U a b
  refine ⟨max B (max (hi - a) (a - lo + 1)), by omega, ?_⟩
  intro t ht₁ ht
  have hu : U.obj.filtration.step (a + t) = ⊥ := by
    apply bot_unique
    rw [← hhi]
    exact U.obj.filtration.antitone_step (by omega)
  have hl : U.obj.filtration.step (a - t + 1) = ⊤ := by
    apply top_unique
    rw [← hlo]
    exact U.obj.filtration.antitone_step (by omega)
  exact ⟨hu, hl, (hb t (by omega)).2.2.1, (hb t (by omega)).2.2.2.1⟩

private noncomputable def cohomologyGraded (R : Type u) [CommRing R] (a : ℤ) :
    FilteredObject (ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj K := K.filtration.gradedPiece a
  map f := FilteredObject.gradedMapSteps f a
  map_id K := FilteredPageProofs.graded_id K a
  map_comp f g := FilteredPageProofs.graded_comp f g a

private theorem imageToGraded_unique (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b r s : ℤ)
    (hr : 1 ≤ r) (hs : 1 ≤ s)
    (c : FilteredPageStationaryComparison R U a b r hr)
    (c' : FilteredPageStationaryComparison R U a b s hs) :
    c.imageToGraded = c'.imageToGraded := by
  apply Iso.ext
  apply (cancel_epi (factorThruImage
    (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)))).1
  exact c.representative_forward.trans c'.representative_forward.symm

private theorem comparison_actual_cycles (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t)
    (c : FilteredPageStationaryComparison R U a b t ht)
    (z : (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).cycles (a + b) ⟶
      (U.obj.filtration.complexCycles a (a + b) t : ModuleCat.{u} R))
    (hz : z ≫ (U.obj.filtration.complexCycles a (a + b) t).arrow =
      (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).iCycles (a + b) ≫
        (U.obj.filtration.complexQuotientπ a (a + 1) (Int.le_add_one le_rfl)).f (a + b)) :
    z ≫ filteredComplexPageπ U.obj.obj U.obj.filtration t (a, b) ≫
        (pageQuotientIso R U a b t ht).inv ≫ c.pageToImage.hom ≫ c.imageToGraded.hom =
      (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).homologyπ (a + b) ≫
        factorThruImageSubobject
          (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a)) := by
  have h : z ≫ filteredComplexPageπ U.obj.obj U.obj.filtration t (a, b) ≫
        (pageQuotientIso R U a b t ht).inv ≫ c.pageToImage.hom =
      (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).homologyπ (a + b) ≫
        factorThruImage
          (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) := by
    apply (cancel_mono (image.ι
      (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)))).1
    simp only [Category.assoc, c.core_normalization, image.fac]
    exact page_actual_cycles_core R U a b t ht z hz
  have hh := congrArg (· ≫ c.imageToGraded.hom) h
  simpa only [Category.assoc, c.representative_forward] using hh

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_successor (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t)
    (hu : U.obj.filtration.step (a + (t + 1)) = ⊥)
    (c : FilteredPageStationaryComparison R U a b t ht)
    (c' : FilteredPageStationaryComparison R U a b (t + 1) (by omega)) :
    (((finiteFilteredPageFunctor R).obj U).page t ht).iCycles (a, b) ≫
        c.pageToImage.hom =
      (((finiteFilteredPageFunctor R).obj U).page t ht).homologyπ (a, b) ≫
        (((finiteFilteredPageFunctor R).obj U).iso t (t + 1) (a, b) rfl ht).hom ≫
        c'.pageToImage.hom := by
  have hmodel := (finiteFilteredPageModel R).successor_spec U a b t ht
  obtain ⟨hZ, f, hfepi, hf⟩ := hmodel.1
  have hfnext := (hmodel.2 _).2 rfl hZ f hf
  obtain ⟨z, hzepi, hz⟩ := actual_cycles_cover U.obj.obj U.obj.filtration a b
    (t + 1)
    (complexStep_bot U.obj.filtration (a + (t + 1)) (a + b + 1) hu)
  have : Epi z := hzepi
  have : Epi f := hfepi
  have hzold : (z ≫ Subobject.ofLE _ _ hZ) ≫
      (U.obj.filtration.complexCycles a (a + b) t).arrow =
      (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ).iCycles (a + b) ≫
        (U.obj.filtration.complexQuotientπ a (a + 1) (Int.le_add_one le_rfl)).f (a + b) := by
    rw [Category.assoc, Subobject.ofLE_arrow]
    exact hz
  apply (cancel_epi (z ≫ f)).1
  apply (cancel_mono c.imageToGraded.hom).1
  have he := imageToGraded_unique R U a b t (t + 1) ht (by omega) c c'
  have hl := comparison_actual_cycles R U a b t ht c (z ≫ Subobject.ofLE _ _ hZ) hzold
  have hr := comparison_actual_cycles R U a b (t + 1) (by omega) c' z hz
  calc
    _ = z ≫ Subobject.ofLE _ _ hZ ≫
        filteredComplexPageπ U.obj.obj U.obj.filtration t (a, b) ≫
        (pageQuotientIso R U a b t ht).inv ≫ c.pageToImage.hom ≫
        c.imageToGraded.hom := by
      simpa only [Category.assoc, filteredComplexPageπ, pageQuotientIso,
        finiteFilteredPageFunctor] using
        congrArg (fun k ↦ z ≫ k ≫ c.pageToImage.hom ≫ c.imageToGraded.hom) hf
    _ = _ := by
      rw [← Category.assoc] at hl
      exact hl
    _ = z ≫ filteredComplexPageπ U.obj.obj U.obj.filtration (t + 1) (a, b) ≫
        (pageQuotientIso R U a b (t + 1) (by omega)).inv ≫
        c'.pageToImage.hom ≫ c'.imageToGraded.hom := hr.symm
    _ = _ := by
      rw [he]
      have hh := congrArg (fun k ↦ z ≫ k ≫
        (pageQuotientIso R U a b (t + 1) (by omega)).inv ≫
        c'.pageToImage.hom ≫ c'.imageToGraded.hom) hfnext
      simpa only [Category.assoc, filteredComplexPageπ, pageQuotientIso,
        Iso.hom_inv_id_assoc, finiteFilteredPageFunctor] using hh.symm

private theorem descended_chain (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C]
    (F : CochainComplex.FiniteFilteredModuleComplex R ⥤ C)
    (G : finiteFilteredModuleDerivedCategory R ⥤ C)
    (e : finiteFilteredDerivedQuotient R ⋙ G ≅ F)
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V) :
    finiteFilteredDescendedMap R F G e ((finiteFilteredDerivedQuotient R).map f) =
      F.map f := by
  dsimp only [finiteFilteredDescendedMap]
  have h := e.inv.naturality f
  change F.map f ≫ e.inv.app V =
    e.inv.app U ≫ G.map ((finiteFilteredDerivedQuotient R).map f) at h
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private noncomputable def localizedRepresentative (R : Type u) [CommRing R]
    (X : finiteFilteredModuleDerivedCategory R) : CochainComplex.FiniteFilteredModuleComplex R :=
  X.as.obj.as

private theorem stationary_naturality_localization (R : Type u) [CommRing R]
    (d : FilteredPageDescentData R) (a b : ℤ)
    (I : finiteFilteredModuleDerivedCategory R ⥤ ModuleCat.{u} R)
    (eI : ∀ U : CochainComplex.FiniteFilteredModuleComplex R,
      I.obj ((finiteFilteredDerivedQuotient R).obj U) ≅
        finiteFilteredQuotientImage R U a (a + b))
    (B : CochainComplex.FiniteFilteredModuleComplex R → ℤ)
    (c : ∀ U t (ht : 1 ≤ t), B U ≤ t → FilteredPageStationaryComparison R U a b t ht)
    (hz : ∀ U t (ht : 1 ≤ t) (_ : B U ≤ t),
      (((finiteFilteredPageFunctor R).obj U).page t ht).d
        (a, b) (a + t, b - t + 1) = 0)
    (hs : ∀ U t (ht : 1 ≤ t) (hU : B U ≤ t),
      (((finiteFilteredPageFunctor R).obj U).page t ht).iCycles (a, b) ≫
          (c U t ht hU).pageToImage.hom =
        (((finiteFilteredPageFunctor R).obj U).page t ht).homologyπ (a, b) ≫
          (((finiteFilteredPageFunctor R).obj U).iso t (t + 1) (a, b) rfl ht).hom ≫
            (c U (t + 1) (by omega) (by omega)).pageToImage.hom)
    (hn : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V)
      (t : ℤ) (ht : 1 ≤ t) (hU : B U ≤ t) (hV : B V ≤ t),
      (((finiteFilteredPageFunctor R).map f).hom t ht).f (a, b) ≫
          (c V t ht hV).pageToImage.hom =
        (c U t ht hU).pageToImage.hom ≫ (eI U).inv ≫
          I.map ((finiteFilteredDerivedQuotient R).map f) ≫ (eI V).hom) :
    ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V)
      (t : ℤ) (ht : 1 ≤ t) (hU : B U ≤ t) (hV : B V ≤ t),
      ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R) d.Sbar d.eS α).hom
          t ht).f (a, b) ≫ (c V t ht hV).pageToImage.hom =
        (c U t ht hU).pageToImage.hom ≫ (eI U).inv ≫ I.map α ≫ (eI V).hom := by
  let W := CochainComplex.finiteFilteredModuleQuasiIso R
  let rep := localizedRepresentative R
  let P (t : ℤ) (ht : 1 ≤ t) := SpectralSequence.pageFunctor (ModuleCat.{u} R)
    (fun r ↦ ComplexShape.up' (r, 1 - r)) 1 t ht
  let er (U : CochainComplex.FiniteFilteredModuleComplex R) (t : ℤ) (ht : 1 ≤ t) :
      ((d.Sbar.obj ((finiteFilteredDerivedQuotient R).obj U)).page t ht) ≅
        (((finiteFilteredPageFunctor R).obj U).page t ht) :=
    (P t ht).mapIso (d.eS.app U)
  let cc (X : finiteFilteredModuleDerivedCategory R) (t : ℤ) (ht : 1 ≤ t)
      (hX : B (rep X) ≤ t) : ((d.Sbar.obj X).page t ht).X (a, b) ≅ I.obj X :=
    (HomologicalComplex.eval _ _ (a, b)).mapIso (er (rep X) t ht) ≪≫
      (c (rep X) t ht hX).pageToImage ≪≫ (eI (rep X)).symm
  have hz' (X : finiteFilteredModuleDerivedCategory R) (t : ℤ) (ht : 1 ≤ t)
      (hX : B (rep X) ≤ t) :
      Epi (((d.Sbar.obj X).page t ht).iCycles (a, b)) := by
    let e : ((d.Sbar.obj X).page t ht) ≅
        (((finiteFilteredPageFunctor R).obj (rep X)).page t ht) := er (rep X) t ht
    have hd : ((d.Sbar.obj X).page t ht).d (a, b) (a + t, b - t + 1) = 0 := by
      apply (cancel_mono (e.hom.f (a + t, b - t + 1))).1
      rw [zero_comp, ← e.hom.comm, hz (rep X) t ht hX, comp_zero]
    have := ((d.Sbar.obj X).page t ht).isIso_iCycles (a, b)
      (a + t, b - t + 1) (by simp [ComplexShape.next]; omega) hd
    infer_instance
  have hs' (X : finiteFilteredModuleDerivedCategory R) (t : ℤ) (ht : 1 ≤ t)
      (hX : B (rep X) ≤ t) :
      ((d.Sbar.obj X).page t ht).iCycles (a, b) ≫ (cc X t ht hX).hom =
        ((d.Sbar.obj X).page t ht).homologyπ (a, b) ≫
          ((d.Sbar.obj X).iso t (t + 1) (a, b) rfl ht).hom ≫
            (cc X (t + 1) (by omega) (by omega)).hom := by
    let U := rep X
    have hU : B U ≤ t := hX
    have hh := hs U t ht hX
    have hcomm := (d.eS.hom.app U).comm t (t + 1) (a, b) rfl ht
    change (((finiteFilteredDerivedQuotient R ⋙ d.Sbar).obj U).page t ht).iCycles
        (a, b) ≫ ((d.eS.hom.app U).hom t ht).f (a, b) ≫
        (c U t ht hX).pageToImage.hom ≫ (eI U).inv =
      (((finiteFilteredDerivedQuotient R ⋙ d.Sbar).obj U).page t ht).homologyπ (a, b) ≫
        (((finiteFilteredDerivedQuotient R ⋙ d.Sbar).obj U).iso
          t (t + 1) (a, b) rfl ht).hom ≫
        ((d.eS.hom.app U).hom (t + 1) (by omega)).f (a, b) ≫
        (c U (t + 1) (by omega) (by omega)).pageToImage.hom ≫ (eI U).inv
    rw [← HomologicalComplex.cyclesMap_i_assoc, reassoc_of% hh,
      ← HomologicalComplex.homologyπ_naturality_assoc, reassoc_of% hcomm]
    rfl
  have hn' {K L : CochainComplex.FiniteFilteredModuleHomotopy R} (f : K ⟶ L) :
      ∃ T : ℤ, ∀ (t : ℤ) (ht : 1 ≤ t)
        (hK : B (rep (W.Q.obj K)) ≤ t) (hL : B (rep (W.Q.obj L)) ≤ t), T ≤ t →
        ((d.Sbar.map (W.Q.map f)).hom t ht).f (a, b) ≫
          (cc (W.Q.obj L) t ht hL).hom =
            (cc (W.Q.obj K) t ht hK).hom ≫ I.map (W.Q.map f) := by
    refine ⟨0, ?_⟩
    intro t ht hK hL hT
    let q := CochainComplex.finiteFilteredModuleHomotopyQuotient R
    have : q.Full := by dsimp [q, CochainComplex.finiteFilteredModuleHomotopyQuotient];
                        infer_instance
    let f' : K.as ⟶ L.as := q.preimage f
    have hh := hn f' t ht hK hL
    have he := congrArg (fun m ↦ (m.hom t ht).f (a, b)) (d.eS.hom.naturality f')
    change ((d.Sbar.map ((finiteFilteredDerivedQuotient R).map f')).hom t ht).f (a, b) ≫
        (er L.as t ht).hom.f (a, b) =
      (er K.as t ht).hom.f (a, b) ≫
        (((finiteFilteredPageFunctor R).map f').hom t ht).f (a, b) at he
    have hmap : (finiteFilteredDerivedQuotient R).map f' = W.Q.map f := by
      change W.Q.map (q.map (q.preimage f)) = _
      rw [Functor.map_preimage]
    rw [← hmap]
    change _ ≫ (er L.as t ht).hom.f (a, b) ≫ _ ≫ _ =
      (er K.as t ht).hom.f (a, b) ≫ _ ≫ _ ≫ _
    change _ ≫ (er L.as t ht).hom.f (a, b) ≫
        (c L.as t ht hL).pageToImage.hom ≫ (eI L.as).inv =
      (er K.as t ht).hom.f (a, b) ≫ (c K.as t ht hK).pageToImage.hom ≫
        (eI K.as).inv ≫ I.map ((finiteFilteredDerivedQuotient R).map f')
    rw [reassoc_of% he, reassoc_of% hh]
    simp only [Iso.hom_inv_id, Category.comp_id]
  intro U V α t ht hU hV
  have hh := localization_stationary_naturality W d.Sbar I a b (fun X ↦ B (rep X))
    cc hz' hs' hn' α t ht hU hV
  apply (cancel_epi ((er U t ht).hom.f (a, b))).1
  apply (cancel_mono (eI V).inv).1
  have heU : ((d.eS.hom.app U).hom t ht).f (a, b) ≫
      ((d.eS.inv.app U).hom t ht).f (a, b) = 𝟙 _ := by
    simpa only [SpectralSequence.comp_hom, HomologicalComplex.comp_f,
      SpectralSequence.id_hom, HomologicalComplex.id_f] using
      congrArg (fun m ↦ (m.hom t ht).f (a, b)) (d.eS.hom_inv_id_app U)
  change ((d.Sbar.map α).hom t ht).f (a, b) ≫
      ((d.eS.hom.app V).hom t ht).f (a, b) ≫ (c V t ht hV).pageToImage.hom ≫
      (eI V).inv =
    ((d.eS.hom.app U).hom t ht).f (a, b) ≫ (c U t ht hU).pageToImage.hom ≫
      (eI U).inv ≫ I.map α at hh
  dsimp only [finiteFilteredDescendedMap]
  simpa only [cc, er, P, rep, localizedRepresentative,
    SpectralSequence.pageFunctor_map, Iso.app_hom, Iso.app_inv,
    reassoc_of% heU, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom,
    HomologicalComplex.eval_map, SpectralSequence.comp_hom, HomologicalComplex.comp_f,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Category.comp_id, Category.id_comp] using hh

/-- Stationary filtered pages identify naturally with graded cohomology images.
Source: Stacks Project, Homology, Tags 012K, 012P and 012W; Categories, Tag 04VK.
(blueprint: lem-kun-filtered-page-stationary).

Proof. Choose uniform filtration bounds lo and hi, and use the bound
max(1, hi-a, a-lo+1). The two outside steps of the quotient window are zero and
the whole complex. Consequently its image cohomology is the image of H(F^a)
in H(U/F^(a+1)). On cycles the kernel is the sum of total boundaries lying in
F^a and cycles in F^(a+1). The graded cohomology image has precisely the same
kernel, so the two epic quotient presentations give the unique isomorphism
satisfying both representative equations. The core image comparison gives the
page comparison with its normalization. A chain map sends each cycle x to f(x),
which proves both chain naturality squares. At stationary indices the normalized
successor comparison also sends x to x, so the comparisons agree on adjacent
pages. Localization is generated by chain maps and inverses of graded
quasi-isomorphisms. The naturality squares are stable under composition and
inversion at a common sufficiently large index. Successor agreement transports
the resulting square down to every index stationary for the two endpoints.
The image functor and its comparisons are obtained from the descended graded
cohomology functor using the representative-normalized isomorphisms. -/
theorem filteredPageStationary (R : Type u) [CommRing R] (d : FilteredPageDescentData R) :
    Nonempty (FilteredPageStationaryData R d) := by
  classical
  let B (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) : ℤ :=
    (stationary_bound_exists R U a b).choose
  have hb (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :
      1 ≤ B U a b ∧ ∀ (t : ℤ) (ht : 1 ≤ t), B U a b ≤ t →
        U.obj.filtration.step (a + t) = ⊥ ∧
        U.obj.filtration.step (a - t + 1) = ⊤ ∧
        (((finiteFilteredPageFunctor R).obj U).page t ht).d
          (a, b) (a + t, b - t + 1) = 0 ∧
        (((finiteFilteredPageFunctor R).obj U).page t ht).d
          (a - t, b + t - 1) (a, b) = 0 :=
    (stationary_bound_exists R U a b).choose_spec
  let c (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ)
      (ht : 1 ≤ t) (hU : B U a b ≤ t) : FilteredPageStationaryComparison R U a b t ht :=
    (stationary_comparison R U a b t ht ((hb U a b).2 t ht hU).1
      ((hb U a b).2 t ht hU).2.1).some
  let eQ (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :=
    (quotient_image_graded R U a (a + b)).choose
  have heQ (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :=
    (quotient_image_graded R U a (a + b)).choose_spec
  have hcQ (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ)
      (ht : 1 ≤ t) (hU : B U a b ≤ t) :
      (c U a b t ht hU).imageToGraded = eQ U a b := by
    apply Iso.ext
    apply (cancel_epi (factorThruImage
      (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)))).1
    exact (c U a b t ht hU).representative_forward.trans (heQ U a b).symm
  let I (a b : ℤ) := d.Hbar (a + b) ⋙ cohomologyGraded R a
  let eI (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :
      (I a b).obj ((finiteFilteredDerivedQuotient R).obj U) ≅
        finiteFilteredQuotientImage R U a (a + b) :=
    (cohomologyGraded R a).mapIso ((d.eH (a + b)).app U) ≪≫ (eQ U a b).symm
  have hiMap {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V) (a b : ℤ) :
      (eI U a b).inv ≫ (I a b).map α ≫ (eI V a b).hom =
        (eQ U a b).hom ≫ FilteredObject.gradedMapSteps
          (finiteFilteredDescendedMap R (finiteFilteredCohomology R (a + b))
            (d.Hbar (a + b)) (d.eH (a + b)) α) a ≫ (eQ V a b).inv := by
    simp only [eI, I, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Functor.comp_map, finiteFilteredDescendedMap, cohomologyGraded,
      FilteredPageProofs.graded_comp, Category.assoc]
  refine ⟨{
    imageDerived := I
    imageComparison := eI
    image_chain := ?_
    bound := B
    stationary_window := fun U a b t ht ↦
      ⟨((hb U a b).2 t (by have := (hb U a b).1; change B U a b ≤ t at ht; omega) ht).1,
        ((hb U a b).2 t (by have := (hb U a b).1; change B U a b ≤ t at ht; omega) ht).2.1⟩
    comparison := c
    stationary_naturality := ?_
    stationary_graded_naturality := ?_
    successor_agreement := ?_
    successor_graded_agreement := ?_
  }⟩
  · intro U V f a b
    rw [reassoc_of% (hiMap ((finiteFilteredDerivedQuotient R).map f) a b)]
    rw [descended_chain]
    exact quotient_image_chain R f a b (eQ U a b) (eQ V a b) (heQ U a b) (heQ V a b)
  · intro U V α a b t ht hU hV
    apply stationary_naturality_localization R d a b (I a b) (fun U ↦ eI U a b)
      (fun U ↦ B U a b) (fun U t ht hU ↦ c U a b t ht hU) _ _ _ α t ht hU hV
    · intro U t ht hU
      exact ((hb U a b).2 t ht hU).2.2.1
    · intro U t ht hU
      exact comparison_successor R U a b t ht
        ((hb U a b).2 (t + 1) (by omega) (by omega)).1
        (c U a b t ht hU) (c U a b (t + 1) (by omega) (by omega))
    · intro U V f t ht hU hV
      rw [hiMap ((finiteFilteredDerivedQuotient R).map f) a b,
        descended_chain, ← hcQ U a b t ht hU, ← hcQ V a b t ht hV]
      exact comparison_chain R f a b t ht (c U a b t ht hU) (c V a b t ht hV)
  · intro U V α a b t ht hU hV
    rw [reassoc_of% (hiMap α a b), hcQ V a b t ht hV, hcQ U a b t ht hU]
    simp only [Iso.inv_hom_id, Category.comp_id]
  · intro U a b t ht hU
    exact comparison_successor R U a b t ht
      ((hb U a b).2 (t + 1) (by omega) (by omega)).1
      (c U a b t ht hU) (c U a b (t + 1) (by omega) (by omega))
  · intro U a b t ht hU
    rw [hcQ U a b t ht hU, hcQ U a b (t + 1) (by omega) (by omega)]

end CategoryTheory
