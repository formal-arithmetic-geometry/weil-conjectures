/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups U1 and G9
-/
module

public import Sheaf.CategoryTheory.FlatFilteredScalarExtension
public import Sheaf.CategoryTheory.FilteredPageTwoModel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis
import Sheaf.CategoryTheory.FilteredPageTwoComparison

/-! # Flat comparison of filtered cochain complexes

Source: Stacks Project, Homology, Tag 0BDU and the filtered-complex functoriality lemma;
Cohomology of Schemes, Tag 02KH (blueprint: lem-pc-flat-filtered-complex-comparison).
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits

private theorem flatStepIso
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (C : FilteredObject (CochainComplex (ModuleCat.{max u v w} A) ℤ)) :
    ∃ s : ∀ p : ℤ,
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
            (C.filtration.step p : CochainComplex (ModuleCat.{max u v w} A) ℤ) ≅
          ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p :
            CochainComplex (ModuleCat.{max u v w} B) ℤ),
      ∀ p : ℤ, (s p).hom ≫
          ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p).arrow =
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
          (C.filtration.step p).arrow := by
  have : PreservesFiniteLimits (ModuleCat.filteredScalarFunctor.{u, v, w} φ) :=
    ModuleCat.filteredScalarFunctor_preservesFiniteLimits φ hφ
  let T := ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)
  have hm (p : ℤ) : Mono (T.map (C.filtration.step p).arrow) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    change Mono ((ModuleCat.filteredScalarFunctor.{u, v, w} φ).map
      ((C.filtration.step p).arrow.f n))
    infer_instance
  have hi (p : ℤ) : IsIso (factorThruImageSubobject
      (T.map (C.filtration.step p).arrow)) := by
    have : Mono (factorThruImageSubobject (T.map (C.filtration.step p).arrow)) :=
      mono_of_mono_fac (imageSubobject_arrow_comp _)
    exact isIso_of_mono_of_epi _
  refine ⟨fun p ↦ asIso (factorThruImageSubobject
    (T.map (C.filtration.step p).arrow)), ?_⟩
  intro p
  exact imageSubobject_arrow_comp _

private theorem flatQuotientIso
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B)
    (C : FilteredObject (CochainComplex (ModuleCat.{max u v w} A) ℤ))
    (s : ∀ p : ℤ,
      (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
          (C.filtration.step p : CochainComplex (ModuleCat.{max u v w} A) ℤ) ≅
        ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p :
          CochainComplex (ModuleCat.{max u v w} B) ℤ))
    (hs : ∀ p : ℤ, (s p).hom ≫
        ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p).arrow =
      (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
        (C.filtration.step p).arrow) :
    ∃ g : ∀ (a b : ℤ) (hab : a ≤ b),
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
            (C.filtration.complexQuotient a b hab) ≅
          (ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.complexQuotient a b hab,
      ∀ (a b : ℤ) (hab : a ≤ b),
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
            (C.filtration.complexQuotientπ a b hab) ≫ (g a b hab).hom =
          (s a).hom ≫
            (ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.complexQuotientπ
              a b hab := by
  let T := ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)
  have : T.Additive := by
    dsimp [T, ModuleCat.filteredScalarComplex]
    infer_instance
  have : PreservesFiniteColimits T := by
    dsimp [T, ModuleCat.filteredScalarComplex]
    infer_instance
  let U := ModuleCat.filteredScalarObject.{u, v, w} φ C
  have hc (a b : ℤ) (hab : a ≤ b) :
      T.map (Subobject.ofLE (C.filtration.step b) (C.filtration.step a)
        (C.filtration.antitone_step hab)) ≫ (s a).hom =
      (s b).hom ≫ Subobject.ofLE (U.filtration.step b) (U.filtration.step a)
        (U.filtration.antitone_step hab) := by
    apply (cancel_mono (U.filtration.step a).arrow).1
    rw [Category.assoc, hs, ← T.map_comp, Subobject.ofLE_arrow,
      Category.assoc, Subobject.ofLE_arrow, hs]
  let g (a b : ℤ) (hab : a ≤ b) :=
    PreservesCokernel.iso T
      (Subobject.ofLE (C.filtration.step b) (C.filtration.step a)
        (C.filtration.antitone_step hab)) ≪≫
      cokernel.mapIso _ _ (s b) (s a) (hc a b hab)
  refine ⟨g, ?_⟩
  intro a b hab
  change T.map (cokernel.π _) ≫ (g a b hab).hom = _
  simp [g, U, DecreasingFiltration.complexQuotientπ, cokernel.mapIso]

private noncomputable def imageComparison
    {CA : Type*} {CB : Type*} [Category* CA] [Category* CB]
    [Abelian CA] [Abelian CB] (L : CA ⥤ CB)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {X Y : CA} {X' Y' : CB} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : L.obj X ≅ X') (b : L.obj Y ≅ Y')
    (h : L.map f ≫ b.hom = a.hom ≫ g) : L.obj (image f) ≅ image g :=
  (PreservesImage.iso L f).symm ≪≫ (im (C := CB)).mapIso
    (Arrow.isoMk (f := Arrow.mk (L.map f)) (g := Arrow.mk g) a b h.symm)

private theorem imageComparison_comm
    {CA : Type*} {CB : Type*} [Category* CA] [Category* CB]
    [Abelian CA] [Abelian CB] (L : CA ⥤ CB)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {X Y : CA} {X' Y' : CB} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : L.obj X ≅ X') (b : L.obj Y ≅ Y')
    (h : L.map f ≫ b.hom = a.hom ≫ g) :
    (imageComparison L f g a b h).hom ≫ image.ι g = L.map (image.ι f) ≫ b.hom := by
  have hm : image.map (Arrow.isoMk (f := Arrow.mk (L.map f))
      (g := Arrow.mk g) a b h.symm).hom ≫ image.ι g =
      image.ι (L.map f) ≫ b.hom := image.map_ι _
  dsimp only [imageComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, im]
  rw [Category.assoc, hm, ← Category.assoc, PreservesImage.inv_comp_image_ι_map]

private theorem flatHomology_naturality
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    {K L : CochainComplex (ModuleCat.{max u v w} A) ℤ} (t : K ⟶ L) (n : ℤ) :
    (ModuleCat.filteredScalarFunctor.{u, v, w} φ).map
        (HomologicalComplex.homologyMap t n) ≫
      (ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ L n).hom =
    (ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ K n).hom ≫
      HomologicalComplex.homologyMap
        ((ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map t) n := by
  have : PreservesFiniteLimits (ModuleCat.filteredScalarFunctor.{u, v, w} φ) :=
    ModuleCat.filteredScalarFunctor_preservesFiniteLimits φ hφ
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map t) _

set_option backward.isDefEq.respectTransparency false in
private theorem model_representative_epi
    {V : Type*} [Category* V] [Abelian V]
    (M : FilteredPageTwoModel V) (U : FilteredObject (CochainComplex V ℤ))
    (p q r : ℤ) (hr : 2 ≤ r)
    (g : (U.filtration.complexCycleRepresentatives p (p + q) r : V) ⟶
      (U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)).cycles (p + q))
    (z : (U.filtration.complexCycleRepresentatives p (p + q) r : V) ⟶
      image (HomologicalComplex.homologyMap (M.φ U p r hr) (p + q)))
    (hg : g ≫ (U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)).iCycles
        (p + q) = (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
      (Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
        (U.filtration.antitone_step (by omega))).f (p + q) ≫
      (U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)).f (p + q))
    (hz : z ≫ image.ι (HomologicalComplex.homologyMap (M.φ U p r hr) (p + q)) =
      g ≫ (U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)).homologyπ
        (p + q)) : Epi z := by
  let S := U.filtration.complexQuotient p (p + r) (by omega)
  let Q := U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)
  obtain ⟨_, a, _, haepi, _, ha⟩ :=
    U.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
  have : Epi a := haepi
  have hga : g = a ≫ HomologicalComplex.cyclesMap (M.φ U p r hr) (p + q) := by
    apply (cancel_mono (Q.iCycles (p + q))).1
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, ha]
    have he := congrArg (fun t ↦ t.f (p + q)) (M.comm_φ U p r hr)
    simp only [HomologicalComplex.comp_f] at he
    simpa only [Category.assoc, he] using hg
  have heq : z = a ≫ S.homologyπ (p + q) ≫
      factorThruImage (HomologicalComplex.homologyMap (M.φ U p r hr) (p + q)) := by
    apply (cancel_mono (image.ι _)).1
    rw [hz, hga]
    simp only [Category.assoc, image.fac, HomologicalComplex.homologyπ_naturality]
  rw [heq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem model_differential_on_representatives
    {V : Type*} [Category* V] [Abelian V]
    (M : FilteredPageTwoModel V) (U : FilteredObject (CochainComplex V ℤ))
    (p q r : ℤ) (hr : 2 ≤ r) {X : V}
    (x : X ⟶ (U.filtration.step p : CochainComplex V ℤ).X (p + q))
    (z : X ⟶ ((M.S.obj U).page r hr).X (p, q))
    (y : X ⟶ (U.filtration.step (p + r) : CochainComplex V ℤ).X
      (p + r + (q + 1 - r)))
    (g : X ⟶ (U.filtration.complexQuotient (p - r + 1) (p + 1)
      (by omega)).cycles (p + q))
    (h : X ⟶ (U.filtration.complexQuotient (p + r - r + 1) (p + r + 1)
      (by omega)).cycles (p + r + (q + 1 - r)))
    (hx : g ≫ (U.filtration.complexQuotient (p - r + 1) (p + 1)
        (by omega)).iCycles (p + q) = x ≫
      (Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
        (U.filtration.antitone_step (by omega))).f (p + q) ≫
      (U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)).f (p + q))
    (hz : z ≫ (M.pageIso U p q r hr).hom ≫
        image.ι (HomologicalComplex.homologyMap (M.φ U p r hr) (p + q)) =
      g ≫ (U.filtration.complexQuotient (p - r + 1) (p + 1)
        (by omega)).homologyπ (p + q))
    (hy : y ≫ (U.filtration.step (p + r)).arrow.f (p + r + (q + 1 - r)) =
      x ≫ (U.filtration.step p).arrow.f (p + q) ≫
        U.obj.d (p + q) (p + r + (q + 1 - r)))
    (hh : h ≫ (U.filtration.complexQuotient (p + r - r + 1) (p + r + 1)
        (by omega)).iCycles (p + r + (q + 1 - r)) = y ≫
      (Subobject.ofLE (U.filtration.step (p + r))
        (U.filtration.step (p + r - r + 1))
        (U.filtration.antitone_step (by omega))).f (p + r + (q + 1 - r)) ≫
      (U.filtration.complexQuotientπ (p + r - r + 1) (p + r + 1)
        (by omega)).f (p + r + (q + 1 - r))) :
    z ≫ ((M.S.obj U).page r hr).d (p, q) (p + r, q + 1 - r) ≫
        (M.pageIso U (p + r) (q + 1 - r) r hr).hom ≫
        image.ι (HomologicalComplex.homologyMap (M.φ U (p + r) r hr)
          (p + r + (q + 1 - r))) =
      h ≫ (U.filtration.complexQuotient (p + r - r + 1) (p + r + 1)
        (by omega)).homologyπ (p + r + (q + 1 - r)) := by
  let R := U.filtration.complexCycleRepresentatives p (p + q) r
  have hf : R.Factors x := by
    apply (pullback_factors_iff _ _ _).mpr
    apply (Subobject.inf_factors _).mpr
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).mpr
      have hn : p + r + (q + 1 - r) = p + q + 1 := by omega
      rw [← hn, Category.assoc, ← hy]
      exact imageSubobject_factors_comp_self _ _
  let ρ := R.factorThru x hf
  have hρ : ρ ≫ R.arrow = x := Subobject.factorThru_arrow _ _ _
  obtain ⟨g₀, z₀, y₀, h₀, hg₀, hz₀, hy₀, hh₀, hd₀⟩ := M.differential U p q r hr
  have hgg : ρ ≫ g₀ = g := by
    apply (cancel_mono ((U.filtration.complexQuotient (p - r + 1) (p + 1)
      (by omega)).iCycles (p + q))).1
    rw [Category.assoc, hg₀, ← Category.assoc, ← Category.assoc, hρ, hx, Category.assoc]
  have hzz : ρ ≫ z₀ ≫ (M.pageIso U p q r hr).inv = z := by
    apply (cancel_mono ((M.pageIso U p q r hr).hom ≫ image.ι _)).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hz₀, ← Category.assoc, hgg, hz]
  have hyy : ρ ≫ y₀ = y := by
    apply (cancel_mono ((U.filtration.step (p + r)).arrow.f
      (p + r + (q + 1 - r)))).1
    rw [Category.assoc, hy₀, ← Category.assoc, ← Category.assoc, hρ, hy, Category.assoc]
  have hhh : ρ ≫ h₀ = h := by
    apply (cancel_mono ((U.filtration.complexQuotient (p + r - r + 1) (p + r + 1)
      (by omega)).iCycles (p + r + (q + 1 - r)))).1
    rw [Category.assoc, hh₀, ← Category.assoc, ← Category.assoc, hyy, hh, Category.assoc]
  rw [← hzz]
  simp only [Category.assoc]
  rw [hd₀, ← Category.assoc, hhh]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def flatCyclesIso
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (K : CochainComplex (ModuleCat.{max u v w} A) ℤ) (n : ℤ) :
    (ModuleCat.filteredScalarFunctor.{u, v, w} φ).obj (K.cycles n) ≅
      ((ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj K).cycles n := by
  letI : PreservesFiniteLimits (ModuleCat.filteredScalarFunctor.{u, v, w} φ) :=
    ModuleCat.filteredScalarFunctor_preservesFiniteLimits φ hφ
  exact (((ShortComplex.LeftHomologyData.canonical (K.sc n)).map
    (ModuleCat.filteredScalarFunctor.{u, v, w} φ)).cyclesIso).symm

set_option backward.isDefEq.respectTransparency false in
private theorem flatCyclesIso_i
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (K : CochainComplex (ModuleCat.{max u v w} A) ℤ) (n : ℤ) :
    (flatCyclesIso A B φ hφ K n).hom ≫
        ((ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj K).iCycles n =
      (ModuleCat.filteredScalarFunctor.{u, v, w} φ).map (K.iCycles n) := by
  have : PreservesFiniteLimits (ModuleCat.filteredScalarFunctor.{u, v, w} φ) :=
    ModuleCat.filteredScalarFunctor_preservesFiniteLimits φ hφ
  exact ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
    ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map
      (ModuleCat.filteredScalarFunctor.{u, v, w} φ))

set_option backward.isDefEq.respectTransparency false in
private theorem flatCyclesIso_π
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (K : CochainComplex (ModuleCat.{max u v w} A) ℤ) (n : ℤ) :
    (ModuleCat.filteredScalarFunctor.{u, v, w} φ).map (K.homologyπ n) ≫
        (ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ K n).hom =
      (flatCyclesIso A B φ hφ K n).hom ≫
        ((ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj K).homologyπ n := by
  have : PreservesFiniteLimits (ModuleCat.filteredScalarFunctor.{u, v, w} φ) :=
    ModuleCat.filteredScalarFunctor_preservesFiniteLimits φ hφ
  let h := ShortComplex.LeftHomologyData.canonical (K.sc n)
  have he : h.homologyIso = Iso.refl _ := by
    apply Iso.ext
    apply (cancel_epi (K.homologyπ n)).1
    change (K.sc n).homologyπ ≫ h.homologyIso.hom = _
    rw [h.homologyπ_comp_homologyIso_hom]
    have hc : h.cyclesIso.hom = 𝟙 _ := by
      apply (cancel_mono (K.iCycles n)).1
      exact h.cyclesIso_hom_comp_i
    simp only [hc, Category.id_comp, Iso.refl_hom]
    rfl
  have he' : (K.sc n).mapHomologyIso
      (ModuleCat.filteredScalarFunctor.{u, v, w} φ) =
      (h.map (ModuleCat.filteredScalarFunctor.{u, v, w} φ)).homologyIso := by
    rw [h.mapHomologyIso_eq]
    dsimp only [h, ShortComplex.LeftHomologyData.canonical_H] at he ⊢
    rw [he]
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.refl_inv]
    change _ ≫ (ModuleCat.filteredScalarFunctor.{u, v, w} φ).map
      (𝟙 ((K.sc n).homology)) = _
    exact (congrArg (fun k ↦
      ((h.map (ModuleCat.filteredScalarFunctor.{u, v, w} φ)).homologyIso.hom) ≫ k)
        ((ModuleCat.filteredScalarFunctor.{u, v, w} φ).map_id _)).trans
          (Category.comp_id _)
  change (ModuleCat.filteredScalarFunctor.{u, v, w} φ).map h.π ≫
    ((K.sc n).mapHomologyIso (ModuleCat.filteredScalarFunctor.{u, v, w} φ)).inv = _
  rw [he']
  exact (h.map (ModuleCat.filteredScalarFunctor.{u, v, w} φ)).π_comp_homologyIso_inv


set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 300000 in
-- Elaborate the simultaneous step, quotient, cycle and page comparison families.
/-- Flat tensor identifies all filtered pages, with their differentials, and an
isomorphism on the induced second-page maps implies an isomorphism on cohomology.
The spectral sequences are any functorial filtered-complex models from page two
(def-sp-filtered-page-two-model); their pages are images of quotient cohomology maps.
The step and quotient-complex isomorphisms are fixed by their inclusion and projection
equations; each page isomorphism is fixed by the image description of the pages,
through canonical flat cohomology base change of the quotient complexes. The graded
quotient isomorphisms also supply the first-page identification.
Source: Stacks Project, Homology, Tag 0BDU and
lemma-spectral-sequence-filtered-complex-functorial; Cohomology of Schemes, Tag 02KH
(blueprint: lem-pc-flat-filtered-complex-comparison).

Proof. Exact scalar extension preserves the filtration inclusions, so their
factorizations through their images are isomorphisms. Preservation of cokernels
then gives the quotient-complex comparisons, characterized by their projection
equations. The flat homology isomorphism is natural in these quotient maps.
Preservation of images identifies the image descriptions of every page. To check
the differentials, use the epimorphism from cycle representatives to the source
page. Transport its cycle lifts and differential lifts through the step and
quotient isomorphisms. The differential normalization of the target model then
gives the desired equality after its monic image inclusion; cancel both maps.
Finally cancel the second-page scalar-extension isomorphisms from the hypothesis
and apply the finite filtered page-two comparison theorem to f. Compose its
cohomology isomorphism with flat homology base change. -/
theorem flatFilteredComplex_comparison
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (C : FilteredObject (CochainComplex (ModuleCat.{max u v w} A) ℤ))
    (D : FilteredObject (CochainComplex (ModuleCat.{max u v w} B) ℤ))
    (hCfin : C.filtration.IsFinite) (hDfin : D.filtration.IsFinite)
    (hC : ∃ N : ℤ, ∀ i : ℤ, i < N → IsZero (C.obj.X i))
    (hD : ∃ N : ℤ, ∀ i : ℤ, i < N → IsZero (D.obj.X i))
    (f : ModuleCat.filteredScalarObject.{u, v, w} φ C ⟶ D)
    (MA : FilteredPageTwoModel (ModuleCat.{max u v w} A))
    (MB : FilteredPageTwoModel (ModuleCat.{max u v w} B)) :
    ∃ (s : ∀ p : ℤ,
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
            (C.filtration.step p : CochainComplex (ModuleCat.{max u v w} A) ℤ) ≅
          ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p :
            CochainComplex (ModuleCat.{max u v w} B) ℤ))
      (g : ∀ (a b : ℤ) (hab : a ≤ b),
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
            (C.filtration.complexQuotient a b hab) ≅
          (ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.complexQuotient a b hab)
      (e : ∀ (r : ℤ) (hr : 2 ≤ r),
        (ModuleCat.filteredScalarComplex.{u, v, w} φ
            (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))).obj ((MA.S.obj C).page r hr) ≅
          (MB.S.obj (ModuleCat.filteredScalarObject.{u, v, w} φ C)).page r hr),
      (∀ p : ℤ, (s p).hom ≫
          ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p).arrow =
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
          (C.filtration.step p).arrow) ∧
      (∀ (a b : ℤ) (hab : a ≤ b), (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
          (C.filtration.complexQuotientπ a b hab) ≫ (g a b hab).hom =
        (s a).hom ≫
          (ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.complexQuotientπ
            a b hab) ∧
      (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (e r hr).hom.f (p, q) ≫
          (MB.pageIso (ModuleCat.filteredScalarObject.{u, v, w} φ C) p q r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (MB.φ (ModuleCat.filteredScalarObject.{u, v, w} φ C) p r hr) (p + q)) =
        (ModuleCat.filteredScalarFunctor.{u, v, w} φ).map
            ((MA.pageIso C p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (MA.φ C p r hr) (p + q))) ≫
          (ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ
            (C.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)) (p + q)).hom ≫
          HomologicalComplex.homologyMap (g (p - r + 1) (p + 1) (by omega)).hom (p + q)) ∧
      ((∀ p q : ℤ, IsIso ((e 2 le_rfl).hom.f (p, q) ≫ ((MB.S.map f).hom 2).f (p, q))) →
        ∀ n : ℤ, IsIso
          ((ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ C.obj n).hom ≫
            HomologicalComplex.homologyMap f.hom n)) := by
  classical
  obtain ⟨s, hs⟩ := flatStepIso A B φ hφ C
  obtain ⟨g, hg⟩ := flatQuotientIso A B φ C s hs
  let L := ModuleCat.filteredScalarFunctor.{u, v, w} φ
  let T := ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)
  let U := ModuleCat.filteredScalarObject.{u, v, w} φ C
  have : PreservesFiniteLimits L := ModuleCat.filteredScalarFunctor_preservesFiniteLimits φ hφ
  have : PreservesFiniteColimits L := by dsimp [L]; infer_instance
  have : T.Additive := by dsimp [T, ModuleCat.filteredScalarComplex]; infer_instance
  have : PreservesFiniteColimits T := by
    dsimp [T, ModuleCat.filteredScalarComplex]
    infer_instance
  have hinc (a b : ℤ) (hab : a ≤ b) :
      T.map (Subobject.ofLE (C.filtration.step b) (C.filtration.step a)
        (C.filtration.antitone_step hab)) ≫ (s a).hom =
      (s b).hom ≫ Subobject.ofLE (U.filtration.step b) (U.filtration.step a)
        (U.filtration.antitone_step hab) := by
    apply (cancel_mono (U.filtration.step a).arrow).1
    rw [Category.assoc, hs, ← T.map_comp, Subobject.ofLE_arrow,
      Category.assoc, Subobject.ofLE_arrow, hs]
  have hquot (p r : ℤ) (hr : 2 ≤ r) :
      T.map (MA.φ C p r hr) ≫ (g (p - r + 1) (p + 1) (by omega)).hom =
        (g p (p + r) (by omega)).hom ≫ MB.φ U p r hr := by
    have : Epi (C.filtration.complexQuotientπ p (p + r) (by omega)) := by
      dsimp only [DecreasingFiltration.complexQuotientπ]
      infer_instance
    apply (cancel_epi (T.map (C.filtration.complexQuotientπ p (p + r) (by omega)))).1
    rw [← T.map_comp_assoc, MA.comm_φ, T.map_comp, Category.assoc, hg,
      ← Category.assoc, hinc (p - r + 1) p (by omega), Category.assoc,
      ← MB.comm_φ U p r hr]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ MB.φ U p r hr) (hg p (p + r) (by omega)).symm
  let H (a b : ℤ) (hab : a ≤ b) (n : ℤ) :=
    ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ
      (C.filtration.complexQuotient a b hab) n ≪≫
        (HomologicalComplex.homologyFunctor _ _ n).mapIso (g a b hab)
  let J (a b : ℤ) (hab : a ≤ b) (n : ℤ) :=
    flatCyclesIso A B φ hφ (C.filtration.complexQuotient a b hab) n ≪≫
      (HomologicalComplex.cyclesFunctor _ _ n).mapIso (g a b hab)
  have hJi (a b : ℤ) (hab : a ≤ b) (n : ℤ) :
      (J a b hab n).hom ≫ (U.filtration.complexQuotient a b hab).iCycles n =
        L.map ((C.filtration.complexQuotient a b hab).iCycles n) ≫ (g a b hab).hom.f n := by
    dsimp only [J, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.cyclesFunctor]
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, flatCyclesIso_i]
  have hJπ (a b : ℤ) (hab : a ≤ b) (n : ℤ) :
      L.map ((C.filtration.complexQuotient a b hab).homologyπ n) ≫ (H a b hab n).hom =
        (J a b hab n).hom ≫ (U.filtration.complexQuotient a b hab).homologyπ n := by
    dsimp only [J, H, Iso.trans_hom, Functor.mapIso_hom,
      HomologicalComplex.cyclesFunctor, HomologicalComplex.homologyFunctor]
    rw [Category.assoc, ← HomologicalComplex.homologyπ_naturality,
      ← Category.assoc, flatCyclesIso_π, Category.assoc]
  have hg' (a b : ℤ) (hab : a ≤ b) (n : ℤ) :
      L.map ((C.filtration.complexQuotientπ a b hab).f n) ≫ (g a b hab).hom.f n =
        (s a).hom.f n ≫ (U.filtration.complexQuotientπ a b hab).f n :=
    congrArg (fun k ↦ k.f n) (hg a b hab)
  have hs' (a n : ℤ) :
      (s a).hom.f n ≫ (U.filtration.step a).arrow.f n =
        L.map ((C.filtration.step a).arrow.f n) :=
    congrArg (fun k ↦ k.f n) (hs a)
  have hinc' (a b : ℤ) (hab : a ≤ b) (n : ℤ) :
      L.map ((Subobject.ofLE (C.filtration.step b) (C.filtration.step a)
        (C.filtration.antitone_step hab)).f n) ≫ (s a).hom.f n =
      (s b).hom.f n ≫ (Subobject.ofLE (U.filtration.step b) (U.filtration.step a)
        (U.filtration.antitone_step hab)).f n :=
    congrArg (fun k ↦ k.f n) (hinc a b hab)
  have hH (p q r : ℤ) (hr : 2 ≤ r) :
      L.map (HomologicalComplex.homologyMap (MA.φ C p r hr) (p + q)) ≫
        (H (p - r + 1) (p + 1) (by omega) (p + q)).hom =
      (H p (p + r) (by omega) (p + q)).hom ≫
        HomologicalComplex.homologyMap (MB.φ U p r hr) (p + q) := by
    dsimp only [H, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor]
    rw [← Category.assoc, flatHomology_naturality, Category.assoc,
      ← HomologicalComplex.homologyMap_comp, hquot, HomologicalComplex.homologyMap_comp,
      Category.assoc]
  let e₀ (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :=
    L.mapIso (MA.pageIso C pq.1 pq.2 r hr) ≪≫
      imageComparison L
        (HomologicalComplex.homologyMap (MA.φ C pq.1 r hr) (pq.1 + pq.2))
        (HomologicalComplex.homologyMap (MB.φ U pq.1 r hr) (pq.1 + pq.2))
        (H pq.1 (pq.1 + r) (by omega) (pq.1 + pq.2))
        (H (pq.1 - r + 1) (pq.1 + 1) (by omega) (pq.1 + pq.2))
        (hH pq.1 pq.2 r hr) ≪≫
      (MB.pageIso U pq.1 pq.2 r hr).symm
  have he₀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) :
      (e₀ r hr (p, q)).hom ≫ (MB.pageIso U p q r hr).hom ≫
        image.ι (HomologicalComplex.homologyMap (MB.φ U p r hr) (p + q)) =
      L.map ((MA.pageIso C p q r hr).hom ≫
        image.ι (HomologicalComplex.homologyMap (MA.φ C p r hr) (p + q))) ≫
        (H (p - r + 1) (p + 1) (by omega) (p + q)).hom := by
    dsimp only [e₀, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [imageComparison_comm, ← Category.assoc, ← L.map_comp]
  have hd (p q r : ℤ) (hr : 2 ≤ r) :
      (e₀ r hr (p, q)).hom ≫ ((MB.S.obj U).page r hr).d (p, q) (p + r, q + 1 - r) =
        L.map (((MA.S.obj C).page r hr).d (p, q) (p + r, q + 1 - r)) ≫
          (e₀ r hr (p + r, q + 1 - r)).hom := by
    obtain ⟨gA, zA, yA, hA, hgA, hzA, hyA, hhA, hdA⟩ := MA.differential C p q r hr
    have : Epi zA := model_representative_epi MA C p q r hr gA zA hgA hzA
    let z := L.map (zA ≫ (MA.pageIso C p q r hr).inv) ≫ (e₀ r hr (p, q)).hom
    let x := L.map (C.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
      (s p).hom.f (p + q)
    let y := L.map yA ≫ (s (p + r)).hom.f (p + r + (q + 1 - r))
    let gB := L.map gA ≫ (J (p - r + 1) (p + 1) (by omega) (p + q)).hom
    let hB := L.map hA ≫
      (J (p + r - r + 1) (p + r + 1) (by omega) (p + r + (q + 1 - r))).hom
    have hx : gB ≫ (U.filtration.complexQuotient (p - r + 1) (p + 1)
        (by omega)).iCycles (p + q) = x ≫
        (Subobject.ofLE (U.filtration.step p) (U.filtration.step (p - r + 1))
          (U.filtration.antitone_step (by omega))).f (p + q) ≫
        (U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)).f (p + q) := by
      dsimp only [gB, x]
      rw [Category.assoc, hJi, ← Category.assoc, ← L.map_comp, hgA]
      simp only [L.map_comp, Category.assoc]
      rw [hg']
      simpa only [Category.assoc] using congrArg
        (fun k ↦ L.map (C.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫ k ≫
          (U.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)).f (p + q))
        (hinc' (p - r + 1) p (by omega) (p + q))
    have hz : z ≫ (MB.pageIso U p q r hr).hom ≫
        image.ι (HomologicalComplex.homologyMap (MB.φ U p r hr) (p + q)) =
        gB ≫ (U.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)).homologyπ
          (p + q) := by
      dsimp only [z, gB]
      rw [Category.assoc, he₀, ← Category.assoc, ← L.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hzA, L.map_comp, Category.assoc, hJπ]
    have hy : y ≫ (U.filtration.step (p + r)).arrow.f (p + r + (q + 1 - r)) =
        x ≫ (U.filtration.step p).arrow.f (p + q) ≫
          U.obj.d (p + q) (p + r + (q + 1 - r)) := by
      change y ≫ (U.filtration.step (p + r)).arrow.f (p + r + (q + 1 - r)) =
        x ≫ (U.filtration.step p).arrow.f (p + q) ≫
          L.map (C.obj.d (p + q) (p + r + (q + 1 - r)))
      have hmap := congrArg (fun k ↦ L.map k) hyA
      simp only [L.map_comp] at hmap
      dsimp only [x, y]
      calc
        _ = L.map yA ≫ L.map ((C.filtration.step (p + r)).arrow.f
            (p + r + (q + 1 - r))) := by rw [Category.assoc, hs']
        _ = L.map (C.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
            L.map ((C.filtration.step p).arrow.f (p + q)) ≫
            L.map (C.obj.d (p + q) (p + r + (q + 1 - r))) := hmap
        _ = _ := by
          rw [← hs' p (p + q)]
          simp only [Category.assoc]
    have hh : hB ≫ (U.filtration.complexQuotient (p + r - r + 1) (p + r + 1)
        (by omega)).iCycles (p + r + (q + 1 - r)) = y ≫
        (Subobject.ofLE (U.filtration.step (p + r))
          (U.filtration.step (p + r - r + 1))
          (U.filtration.antitone_step (by omega))).f (p + r + (q + 1 - r)) ≫
        (U.filtration.complexQuotientπ (p + r - r + 1) (p + r + 1) (by omega)).f
          (p + r + (q + 1 - r)) := by
      dsimp only [hB, y]
      rw [Category.assoc, hJi, ← Category.assoc, ← L.map_comp, hhA]
      simp only [L.map_comp, Category.assoc]
      rw [hg']
      simpa only [Category.assoc] using congrArg
        (fun k ↦ L.map yA ≫ k ≫
          (U.filtration.complexQuotientπ (p + r - r + 1) (p + r + 1)
            (by omega)).f (p + r + (q + 1 - r)))
        (hinc' (p + r - r + 1) (p + r) (by omega) (p + r + (q + 1 - r)))
    have hdB := model_differential_on_representatives MB U p q r hr x z y gB hB
      hx hz hy hh
    apply (cancel_epi (L.map (zA ≫ (MA.pageIso C p q r hr).inv))).1
    apply (cancel_mono ((MB.pageIso U (p + r) (q + 1 - r) r hr).hom ≫
      image.ι (HomologicalComplex.homologyMap (MB.φ U (p + r) r hr)
        (p + r + (q + 1 - r))))).1
    simp only [Category.assoc]
    rw [← Category.assoc _ (e₀ r hr (p, q)).hom, hdB]
    rw [he₀, ← Category.assoc, ← L.map_comp, ← Category.assoc, ← L.map_comp]
    simp only [Category.assoc]
    rw [hdA]
    dsimp only [hB]
    rw [L.map_comp]
    simpa only [Category.assoc] using congrArg (fun k ↦ L.map hA ≫ k)
      (hJπ (p + r - r + 1) (p + r + 1) (by omega) (p + r + (q + 1 - r))).symm
  let e (r : ℤ) (hr : 2 ≤ r) :
      (ModuleCat.filteredScalarComplex.{u, v, w} φ
        (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))).obj ((MA.S.obj C).page r hr) ≅
        (MB.S.obj U).page r hr :=
    HomologicalComplex.Hom.isoOfComponents
      (C₁ := (L.mapHomologicalComplex
        (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))).obj ((MA.S.obj C).page r hr))
      (C₂ := (MB.S.obj U).page r hr) (e₀ r hr)
    (by
      rintro ⟨p, q⟩ ⟨p', q'⟩ hij
      change (e₀ r hr (p, q)).hom ≫ ((MB.S.obj U).page r hr).d (p, q) (p', q') =
        L.map (((MA.S.obj C).page r hr).d (p, q) (p', q')) ≫
          (e₀ r hr (p', q')).hom
      have hij' : (p + r, q + (1 - r)) = (p', q') := hij
      cases hij'
      have hq : q + (1 - r) = q + 1 - r := by omega
      rw [hq]
      exact hd p q r hr)
  refine ⟨s, g, e, hs, hg, ?_, ?_⟩
  · intro r hr p q
    exact he₀ r hr p q
  · intro hf n
    have hi (p q : ℤ) : IsIso (((MB.S.map f).hom 2).f (p, q)) := by
      have := hf p q
      have : IsIso ((e 2 le_rfl).hom.f (p, q)) := (e₀ 2 le_rfl (p, q)).isIso_hom
      exact IsIso.of_isIso_comp_left ((e 2 le_rfl).hom.f (p, q)) _
    have : IsIso (HomologicalComplex.homologyMap f.hom n) :=
      filteredPageTwoModel_comparison MB f
        (ModuleCat.filteredScalarObject_isFinite φ C hCfin) hDfin hi n
    have : IsIso (ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ C.obj n).hom :=
      (ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ C.obj n).isIso_hom
    infer_instance

end CategoryTheory
