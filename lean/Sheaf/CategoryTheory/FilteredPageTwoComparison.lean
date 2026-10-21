/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.CategoryTheory.FilteredPageTwoModel
import Sheaf.CategoryTheory.FilteredComplexCanonicalModel
import WeilConjectures.CategoryTheory.FilteredStationaryCycleComparison
import WeilConjectures.CategoryTheory.FilteredCohomologyImage
import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis

/-! # Comparison of finite filtered page-two models

Source: Stacks Project, Homology, Tags 012K, 012Q, 012W and 015K.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {V : Type u} [Category.{v} V] [Abelian V]

private theorem model_quotient_eq (M : FilteredPageTwoModel V)
    (U : FilteredObject (CochainComplex V ℤ)) (p r : ℤ) (hr : 2 ≤ r) :
    M.φ U p r hr = filteredComplexCanonicalQuotientMap U p r hr := by
  have hp : p ≤ p + r := by omega
  have : Epi (U.filtration.complexQuotientπ p (p + r) hp) := by
    dsimp only [DecreasingFiltration.complexQuotientπ]
    infer_instance
  apply (cancel_epi (U.filtration.complexQuotientπ p (p + r) hp)).1
  exact (M.comm_φ U p r hr).trans (filteredComplexCanonicalQuotientMap_comm U p r hr).symm

private noncomputable def model_quotient_iso (M : FilteredPageTwoModel V)
    (U : FilteredObject (CochainComplex V ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    ((M.S.obj U).page r hr).X (p, q) ≅
      filteredComplexPageObject U.obj U.filtration r (p, q) :=
  M.pageIso U p q r hr ≪≫ eqToIso (congrArg
    (fun t ↦ image (HomologicalComplex.homologyMap t (p + q)))
    (model_quotient_eq M U p r hr)) ≪≫
      (filteredComplexCanonicalImageIso U p q r hr).symm

private theorem image_eq_transport {X Y : V} {f g : X ⟶ Y} (h : f = g) :
    eqToHom (congrArg (fun t ↦ image t) h).symm ≫ image.ι f = image.ι g := by
  subst g
  simp

private theorem model_quotient_iso_comm (M : FilteredPageTwoModel V)
    (U : FilteredObject (CochainComplex V ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    (model_quotient_iso M U p q r hr).inv ≫ (M.pageIso U p q r hr).hom ≫
      image.ι (HomologicalComplex.homologyMap (M.φ U p r hr) (p + q)) =
    (filteredComplexCanonicalImageIso U p q r hr).hom ≫
      image.ι (HomologicalComplex.homologyMap
        (filteredComplexCanonicalQuotientMap U p r hr) (p + q)) := by
  dsimp only [model_quotient_iso, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, eqToIso.inv]
  rw [image_eq_transport]
  exact congrArg (fun t ↦ HomologicalComplex.homologyMap t (p + q))
    (model_quotient_eq M U p r hr)

private theorem actual_cycle_normalization (M : FilteredPageTwoModel V)
    (U : FilteredObject (CochainComplex V ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (z : (U.filtration.step p : CochainComplex V ℤ).cycles (p + q) ⟶
      (U.filtration.complexCycles p (p + q) r : V))
    (hz : z ≫ (U.filtration.complexCycles p (p + q) r).arrow =
      (U.filtration.step p : CochainComplex V ℤ).iCycles (p + q) ≫
        (U.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q)) :
    z ≫ filteredComplexPageπ U.obj U.filtration r (p, q) ≫
      (model_quotient_iso M U p q r hr).inv ≫ (M.pageIso U p q r hr).hom ≫
        image.ι (HomologicalComplex.homologyMap (M.φ U p r hr) (p + q)) =
      HomologicalComplex.cyclesMap (U.filtration.complexQuotientπ p (p + r)
        (by omega)) (p + q) ≫
        (U.filtration.complexQuotient p (p + r) (by omega)).homologyπ (p + q) ≫
          HomologicalComplex.homologyMap (M.φ U p r hr) (p + q) := by
  let K := (U.filtration.step p : CochainComplex V ℤ)
  let R := U.filtration.complexCycleRepresentatives p (p + q) r
  have hzero : K.iCycles (p + q) ≫ (U.filtration.step p).arrow.f (p + q) ≫
      U.obj.d (p + q) (p + q + 1) = 0 := by
    rw [(U.filtration.step p).arrow.comm, ← Category.assoc,
      HomologicalComplex.iCycles_d, zero_comp]
  have hf : R.Factors (K.iCycles (p + q)) := by
    apply (pullback_factors_iff _ _ _).mpr
    apply (Subobject.inf_factors _).mpr
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).mpr
      rw [Category.assoc, hzero]
      exact Subobject.factors_zero
  let ρ := R.factorThru (K.iCycles (p + q)) hf
  have hρ : ρ ≫ R.arrow = K.iCycles (p + q) := Subobject.factorThru_arrow _ _ _
  obtain ⟨zR, a, _, _, hzR, ha⟩ :=
    U.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
  have hzz : ρ ≫ zR = z := by
    apply (cancel_mono (U.filtration.complexCycles p (p + q) r).arrow).1
    rw [Category.assoc, hzR, ← Category.assoc, hρ, hz]
  have haa : ρ ≫ a = HomologicalComplex.cyclesMap
      (U.filtration.complexQuotientπ p (p + r) (by omega)) (p + q) := by
    apply (cancel_mono ((U.filtration.complexQuotient p (p + r)
      (by omega)).iCycles (p + q))).1
    rw [Category.assoc, ha, ← Category.assoc, hρ, HomologicalComplex.cyclesMap_i]
  have hn := filteredComplexCanonicalImageIso_property U p q r hr zR a hzR ha
  have hh := congrArg (fun k ↦ ρ ≫ k) hn
  simp only [← Category.assoc] at hh
  rw [hzz, haa] at hh
  simp only [Category.assoc] at hh
  rw [model_quotient_iso_comm, model_quotient_eq]
  exact hh

private theorem stationary_model_comparison (M : FilteredPageTwoModel V)
    (U : FilteredObject (CochainComplex V ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (hu : U.filtration.complexStep (p + r) (p + q + 1) = ⊥)
    (hl : U.filtration.complexStep (p - r + 1) (p + q - 1) = ⊤) :
    ∃ (e : ((M.S.obj U).page r hr).X (p, q) ≅
        (U.filtration.homologyFiltration (p + q)).gradedPiece p)
      (z : (U.filtration.step p : CochainComplex V ℤ).cycles (p + q) ⟶
        ((M.S.obj U).page r hr).X (p, q)), Epi z ∧
      z ≫ e.hom = (U.filtration.step p : CochainComplex V ℤ).homologyπ (p + q) ≫
        factorThruImageSubobject (HomologicalComplex.homologyMap
          (U.filtration.step p).arrow (p + q)) ≫ cokernel.π
          (Subobject.ofLE ((U.filtration.homologyFiltration (p + q)).step (p + 1))
            ((U.filtration.homologyFiltration (p + q)).step p)
            ((U.filtration.homologyFiltration (p + q)).antitone_step (by omega))) ∧
      z ≫ (M.pageIso U p q r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap (M.φ U p r hr) (p + q)) =
        HomologicalComplex.cyclesMap (U.filtration.complexQuotientπ p (p + r)
          (by omega)) (p + q) ≫
          (U.filtration.complexQuotient p (p + r) (by omega)).homologyπ (p + q) ≫
            HomologicalComplex.homologyMap (M.φ U p r hr) (p + q) := by
  let F := U.filtration.homologyFiltration (p + q)
  let a := fun i ↦ factorThruImageSubobject
    (HomologicalComplex.homologyMap (U.filtration.step i).arrow (p + q))
  have ha (i : ℤ) : a i ≫ (F.step i).arrow =
      HomologicalComplex.homologyMap (U.filtration.step i).arrow (p + q) ≫
        (Iso.refl _).hom := by
    dsimp only [a, F, DecreasingFiltration.homologyFiltration]
    simp only [Iso.refl_hom, Category.comp_id]
    exact imageSubobject_arrow_comp _
  have hepi (i : ℤ) : Epi (a i) := by dsimp [a]; infer_instance
  obtain ⟨z₀, e₀, hz₀, hzi, hze⟩ := filteredStationary_cycle_comparison U.obj U.filtration
    p q r (by omega) hu hl (Iso.refl _) F a ha hepi
  have : Epi z₀ := hz₀
  have : Epi (filteredComplexPageπ U.obj U.filtration r (p, q)) := by
    dsimp only [filteredComplexPageπ]
    infer_instance
  let e := model_quotient_iso M U p q r hr ≪≫ e₀
  let z := z₀ ≫ filteredComplexPageπ U.obj U.filtration r (p, q) ≫
    (model_quotient_iso M U p q r hr).inv
  refine ⟨e, z, by dsimp [z]; infer_instance, ?_, ?_⟩
  · dsimp only [e, z, Iso.trans_hom]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hze
  · simpa only [z, Category.assoc] using actual_cycle_normalization M U p q r hr z₀ hzi

private theorem model_pages_iso (M : FilteredPageTwoModel V)
    {U W : FilteredObject (CochainComplex V ℤ)} (f : U ⟶ W)
    (h₂ : ∀ p q : ℤ, IsIso (((M.S.map f).hom 2).f (p, q))) :
    ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), IsIso (((M.S.map f).hom r hr).f (p, q)) := by
  intro r
  refine Int.inductionOn' r 2 ?_ ?_ ?_
  · intro _
    exact h₂
  · intro r hr ih _ p q
    have : ∀ pq : ℤ × ℤ, IsIso (((M.S.map f).hom r hr).f pq) :=
      fun pq ↦ ih hr pq.1 pq.2
    have : IsIso ((M.S.map f).hom r hr) := HomologicalComplex.Hom.isIso_of_components _
    have : IsIso (HomologicalComplex.homologyMap ((M.S.map f).hom r hr) (p, q)) :=
      inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor V _ (p, q)).map
        ((M.S.map f).hom r hr)))
    have hc := (M.S.map f).comm r (r + 1) (p, q) rfl hr
    have : IsIso (((M.S.obj U).iso r (r + 1) (p, q) rfl hr).hom ≫
        ((M.S.map f).hom (r + 1) (by omega)).f (p, q)) := by
      rw [← hc]
      infer_instance
    exact IsIso.of_isIso_comp_left ((M.S.obj U).iso r (r + 1) (p, q) rfl hr).hom _
  · intro r hr _ hr'
    omega

private theorem finite_degree_bounds (U : FilteredObject (CochainComplex V ℤ))
    (hU : U.filtration.IsFinite) :
    ∃ lo hi : ℤ, ∀ n : ℤ,
      U.filtration.complexStep lo n = ⊤ ∧ U.filtration.complexStep hi n = ⊥ := by
  obtain ⟨lo, hi, hlo, hhi⟩ := hU
  change U.filtration.step lo = ⊤ at hlo
  change U.filtration.step hi = ⊥ at hhi
  refine ⟨lo, hi, fun n ↦ ⟨?_, ?_⟩⟩
  · have : IsIso (U.filtration.step lo).arrow := by
      rw [hlo]
      infer_instance
    have : IsIso ((U.filtration.step lo).arrow.f n) :=
      inferInstanceAs (IsIso ((HomologicalComplex.eval V _ n).map
        (U.filtration.step lo).arrow))
    exact (imageSubobject_mono _).trans (Subobject.mk_eq_top_of_isIso _)
  · have hz : (U.filtration.step hi).arrow = 0 := by
      rw [hhi]
      exact Subobject.bot_arrow
    have hz' := congrArg (fun k ↦ k.f n) hz
    change (U.filtration.step hi).arrow.f n = 0 at hz'
    dsimp only [DecreasingFiltration.complexStep]
    simpa only [imageSubobject_zero] using congrArg
      (fun k : (U.filtration.step hi : CochainComplex V ℤ).X n ⟶ U.obj.X n ↦
        imageSubobject k) hz'

private noncomputable def cohomologyFilteredMap
    {U W : FilteredObject (CochainComplex V ℤ)} (f : U ⟶ W) (n : ℤ) :
    (⟨U.obj.homology n, U.filtration.homologyFiltration n⟩ : FilteredObject V) ⟶
      (⟨W.obj.homology n, W.filtration.homologyFiltration n⟩ : FilteredObject V) where
  hom := HomologicalComplex.homologyMap f.hom n
  preserves p := by
    obtain ⟨s, hs⟩ := f.preserves p
    let sq : Arrow.mk (HomologicalComplex.homologyMap (U.filtration.step p).arrow n) ⟶
        Arrow.mk (HomologicalComplex.homologyMap (W.filtration.step p).arrow n) :=
      Arrow.homMk (HomologicalComplex.homologyMap s n)
        (HomologicalComplex.homologyMap f.hom n) (by
          dsimp only [Arrow.mk_hom]
          rw [← HomologicalComplex.homologyMap_comp, hs,
            HomologicalComplex.homologyMap_comp])
    exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩

private theorem cohomology_restriction_naturality
    {U W : FilteredObject (CochainComplex V ℤ)} (f : U ⟶ W) (n p : ℤ)
    (s : (U.filtration.step p : CochainComplex V ℤ) ⟶
      (W.filtration.step p : CochainComplex V ℤ))
    (hs : s ≫ (W.filtration.step p).arrow = (U.filtration.step p).arrow ≫ f.hom) :
    factorThruImageSubobject (HomologicalComplex.homologyMap (U.filtration.step p).arrow n) ≫
        FilteredObject.restrictionSteps (cohomologyFilteredMap f n) p =
      HomologicalComplex.homologyMap s n ≫
        factorThruImageSubobject (HomologicalComplex.homologyMap
          (W.filtration.step p).arrow n) := by
  apply (cancel_mono ((W.filtration.homologyFiltration n).step p).arrow).1
  rw [Category.assoc, show FilteredObject.restrictionSteps (cohomologyFilteredMap f n) p ≫
      ((W.filtration.homologyFiltration n).step p).arrow =
      ((U.filtration.homologyFiltration n).step p).arrow ≫
        HomologicalComplex.homologyMap f.hom n from
      Classical.choose_spec ((cohomologyFilteredMap f n).preserves p)]
  change factorThruImageSubobject
      (HomologicalComplex.homologyMap (U.filtration.step p).arrow n) ≫
        (imageSubobject (HomologicalComplex.homologyMap (U.filtration.step p).arrow n)).arrow ≫
          HomologicalComplex.homologyMap f.hom n =
    (HomologicalComplex.homologyMap s n ≫ factorThruImageSubobject
      (HomologicalComplex.homologyMap (W.filtration.step p).arrow n)) ≫
        (imageSubobject (HomologicalComplex.homologyMap (W.filtration.step p).arrow n)).arrow
  rw [← Category.assoc, imageSubobject_arrow_comp, Category.assoc,
    imageSubobject_arrow_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, hs]

private theorem complexStep_antitone (U : FilteredObject (CochainComplex V ℤ)) (n : ℤ) :
    Antitone (fun p ↦ U.filtration.complexStep p n) := by
  intro p q hpq
  have h := imageSubobject_comp_le
    ((Subobject.ofLE (U.filtration.step q) (U.filtration.step p)
      (U.filtration.antitone_step hpq)).f n) ((U.filtration.step p).arrow.f n)
  simpa only [DecreasingFiltration.complexStep, ← HomologicalComplex.comp_f,
    Subobject.ofLE_arrow] using h

/-- A page-two isomorphism of finite filtered complexes is a cohomology isomorphism.
Source: Stacks Project, Homology, Tags 012K, 012Q, 012W and 015K.
(blueprint: lem-sp-filtered-page-two-comparison).

Proof. A page-two isomorphism propagates to every page, since the next page is
homology of the current page and the transition isomorphisms are natural.
Fix a total degree and a filtration index. Choose a page beyond the common finite
bounds of both filtrations. The stationary cycle comparison identifies that page
with the graded piece of the cohomology-image filtration. Its normalization on
actual cycles, together with the quotient-image description of the model and its
naturality equation, identifies the page map with the induced graded cohomology
map. The maps from actual cycles onto the stationary pages are epic, so checking
that equality on these representatives suffices. Consequently every graded map
of cohomology-image filtrations is an isomorphism. Those filtrations are finite;
finite-filtration induction implies that the underlying cohomology map is an
isomorphism. No boundedness assumption on the complex is needed. -/
theorem filteredPageTwoModel_comparison (M : FilteredPageTwoModel V)
    {U W : FilteredObject (CochainComplex V ℤ)} (f : U ⟶ W)
    (hU : U.filtration.IsFinite) (hW : W.filtration.IsFinite)
    (h₂ : ∀ p q : ℤ, IsIso (((M.S.map f).hom 2).f (p, q))) :
    ∀ n : ℤ, IsIso (HomologicalComplex.homologyMap f.hom n) := by
  classical
  have hpages := model_pages_iso M f h₂
  obtain ⟨loU, hiU, hbU⟩ := finite_degree_bounds U hU
  obtain ⟨loW, hiW, hbW⟩ := finite_degree_bounds W hW
  intro n
  let F : FilteredObject V := ⟨U.obj.homology n, U.filtration.homologyFiltration n⟩
  let G : FilteredObject V := ⟨W.obj.homology n, W.filtration.homologyFiltration n⟩
  let t := cohomologyFilteredMap f n
  have hF : F.filtration.IsFinite := U.filtration.cohomologyImage_isFinite
    (fun i ↦ ⟨loU, hiU, hbU i⟩) n
  have hG : G.filtration.IsFinite := W.filtration.cohomologyImage_isFinite
    (fun i ↦ ⟨loW, hiW, hbW i⟩) n
  apply (FilteredObject.finite_filtration_induction_steps F G t hF hG ?_).1
  intro p
  let q := n - p
  have hn : p + q = n := by dsimp [q]; omega
  let r := max 2 (max (max hiU hiW - p) (p + 1 - min loU loW))
  have hr : 2 ≤ r := le_max_left _ _
  have huU : U.filtration.complexStep (p + r) (p + q + 1) = ⊥ := by
    apply bot_unique
    rw [← (hbU (p + q + 1)).2]
    apply complexStep_antitone
    dsimp [r]
    omega
  have hlU : U.filtration.complexStep (p - r + 1) (p + q - 1) = ⊤ := by
    apply top_unique
    rw [← (hbU (p + q - 1)).1]
    apply complexStep_antitone
    dsimp [r]
    omega
  have huW : W.filtration.complexStep (p + r) (p + q + 1) = ⊥ := by
    apply bot_unique
    rw [← (hbW (p + q + 1)).2]
    apply complexStep_antitone
    dsimp [r]
    omega
  have hlW : W.filtration.complexStep (p - r + 1) (p + q - 1) = ⊤ := by
    apply top_unique
    rw [← (hbW (p + q - 1)).1]
    apply complexStep_antitone
    dsimp [r]
    omega
  obtain ⟨eU, zU, hzUepi, hzeU, hznU⟩ := stationary_model_comparison M U p q r hr huU hlU
  obtain ⟨eW, zW, hzWepi, hzeW, hznW⟩ := stationary_model_comparison M W p q r hr huW hlW
  have : Epi zU := hzUepi
  obtain ⟨s, a, b, hs, ha, hb, hφ, hnat⟩ := M.naturality f p q r hr
  have hzsq : zU ≫ ((M.S.map f).hom r hr).f (p, q) =
      HomologicalComplex.cyclesMap (s p) (p + q) ≫ zW := by
    apply (cancel_mono ((M.pageIso W p q r hr).hom ≫
      image.ι (HomologicalComplex.homologyMap (M.φ W p r hr) (p + q)))).1
    simp only [Category.assoc]
    rw [hnat]
    have hleft := congrArg (fun k ↦ k ≫ HomologicalComplex.homologyMap b (p + q)) hznU
    simp only [Category.assoc] at hleft
    rw [hleft, hφ]
    rw [← HomologicalComplex.homologyπ_naturality_assoc,
      ← HomologicalComplex.homologyMap_comp_assoc, ha,
      HomologicalComplex.homologyMap_comp, hznW]
    simp only [HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, Category.assoc]
  have hat := cohomology_restriction_naturality f (p + q) p (s p) (hs p)
  have hgraded := Classical.choose_spec (FilteredObject.exists_gradedMap_steps
    (⟨U.obj.homology (p + q), U.filtration.homologyFiltration (p + q)⟩ : FilteredObject V)
    (⟨W.obj.homology (p + q), W.filtration.homologyFiltration (p + q)⟩ : FilteredObject V)
    (cohomologyFilteredMap f (p + q)) p)
  change cokernel.π _ ≫ FilteredObject.gradedMapSteps
    (cohomologyFilteredMap f (p + q)) p = _ at hgraded
  have hsq : ((M.S.map f).hom r hr).f (p, q) ≫ eW.hom = eU.hom ≫
      FilteredObject.gradedMapSteps (cohomologyFilteredMap f (p + q)) p := by
    apply (cancel_epi zU).1
    rw [← Category.assoc, hzsq, Category.assoc, hzeW,
      ← HomologicalComplex.homologyπ_naturality_assoc,
      ← Category.assoc (HomologicalComplex.homologyMap (s p) (p + q)), ← hat]
    rw [Category.assoc, ← hgraded]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ FilteredObject.gradedMapSteps (cohomologyFilteredMap f (p + q)) p)
      hzeU.symm
  have : IsIso (((M.S.map f).hom r hr).f (p, q)) := hpages r hr p q
  have : IsIso (eU.hom ≫ FilteredObject.gradedMapSteps
      (cohomologyFilteredMap f (p + q)) p) := by
    rw [← hsq]
    infer_instance
  have hi := IsIso.of_isIso_comp_left eU.hom
    (FilteredObject.gradedMapSteps (cohomologyFilteredMap f (p + q)) p)
  change IsIso (FilteredObject.gradedMapSteps (cohomologyFilteredMap f n) p)
  exact hn ▸ hi

end CategoryTheory
