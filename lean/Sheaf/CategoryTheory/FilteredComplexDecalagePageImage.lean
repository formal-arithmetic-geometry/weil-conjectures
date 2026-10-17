/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalagePageData
import Sheaf.CategoryTheory.FilteredComplexDecalageLeftRepresentatives
import Sheaf.CategoryTheory.FilteredComplexDecalageIntervalMaps
import all Sheaf.CategoryTheory.FilteredComplexDecalagePageData

/-! # Image of decalage cycle representatives

Source: Stacks Project, Tags 012K and 015X.
(blueprint: lem-sp-filtered-complex-decalage-page-image).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem spectral_page_image_factor
    (X : Abelian.SpectralObject C EInt) {i₀ i₁ i₂ i₃ : EInt}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃) (n : ℤ) :
    (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ (Subsingleton.elim _ _) (n - 1) n (n + 1)).g ≫
        (X.kernelSequenceE f₁ f₂ f₃ f₂₃ (Subsingleton.elim _ _) (n - 1) n (n + 1)).f =
      (X.H n).map (ComposableArrows.homMk₁ (F := ComposableArrows.mk₁ f₁₂)
        (G := ComposableArrows.mk₁ f₂₃) f₁ f₃ (Subsingleton.elim _ _)) := by
  simp only [Abelian.SpectralObject.cokernelSequenceE_g,
    Abelian.SpectralObject.kernelSequenceE_f, Category.assoc,
    Abelian.SpectralObject.πE_ιE_assoc, Abelian.SpectralObject.toCycles_i_assoc,
    Abelian.SpectralObject.p_fromOpcycles]
  rw [← Functor.map_comp]
  congr 1

private theorem representative_image_of_left_interval
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (a b : ℤ) (ha : a + (p + q) = p) (hb : b + (p + q + 1) = p + r)
    (hba : a ≤ b) (haa : 1 - (q + (r - 1)) ≤ a)
    (f : U.filtration.decalage.complexQuotient a b hba ⟶
      U.filtration.decalage.complexQuotient (1 - (q + (r - 1))) (1 - q) (by omega))
    (hf : U.filtration.decalage.complexQuotientπ a b hba ≫ f =
      Subobject.ofLE (U.filtration.decalage.step a)
        (U.filtration.decalage.step (1 - (q + (r - 1))))
        (U.filtration.decalage.antitone_step haa) ≫
      U.filtration.decalage.complexQuotientπ (1 - (q + (r - 1))) (1 - q) (by omega)) :
    imageSubobject (filteredComplexDecalageRepresentativeClass U p q r hr) =
      imageSubobject (HomologicalComplex.homologyMap f (p + q)) := by
  let F := U.filtration
  let D := F.decalage
  let n := p + q
  let a' := 1 - (q + (r - 1))
  let L := D.complexQuotient a b hba
  let Q := D.complexQuotient a' (1 - q) (by dsimp [a']; omega)
  let l := Subobject.ofLE (D.step a) (D.step a') (D.antitone_step haa)
  let R := F.complexCycleRepresentatives p n r
  have hka : (D.complexStep a n).Factors (R.arrow ≫ (F.step p).arrow.f n) := by
    have hea : a = -q := by omega
    rw [hea]
    exact representative_factors_decalage U p q r (by omega)
  rw [DecreasingFiltration.complexStep, imageSubobject_mono,
    Subobject.mk_factors_iff] at hka
  obtain ⟨k, hk⟩ : ∃ k : (R : C) ⟶ (D.step a : CochainComplex C ℤ).X n,
      k ≫ (D.step a).arrow.f n = R.arrow ≫ (F.step p).arrow.f n := hka
  obtain ⟨g, hge, hg⟩ := filteredComplexDecalageLeftRepresentatives U p q r hr a b ha hb k hk
  have : Epi g := hge
  have hkl : k ≫ l.f n = filteredComplexDecalageRepresentative U p q r (by omega) ≫
      (Subobject.ofLE (D.step (-q)) (D.step a')
        (D.antitone_step (by dsimp [a']; omega))).f n := by
    apply (cancel_mono ((D.step a').arrow.f n)).1
    simp only [Category.assoc, l, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
    exact hk.trans (filteredComplexDecalageRepresentative_arrow U p q r (by omega)).symm
  have hgmap : g ≫ HomologicalComplex.cyclesMap f n =
      filteredComplexDecalageRepresentativeCycle U p q r hr a' (by dsimp [a']; omega) := by
    apply (cancel_mono (Q.iCycles n)).1
    have hfn := congrArg (fun f ↦ f.f n) hf
    simp only [HomologicalComplex.comp_f] at hfn
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hg]
    rw [Category.assoc, hfn, ← Category.assoc, hkl]
    simpa only [Category.assoc] using
      (filteredComplexDecalageRepresentativeCycle_i U p q r hr a'
        (by dsimp [a']; omega)).symm
  have hc : (g ≫ L.homologyπ n) ≫ HomologicalComplex.homologyMap f n =
      filteredComplexDecalageRepresentativeClass U p q r hr := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hgmap]
    rfl
  rw [← hc, imageSubobject_comp_of_epi]

/-- The spectral-object page embedded in right-interval cohomology is precisely the
image of original filtered-cycle representatives.
Source: Stacks Project, Tag 012K, cycle formula; Tag 015X, Remark 13.26.15.
(blueprint: lem-sp-filtered-complex-decalage-page-image).

Proof. Put n=p+q and D=Dec(F). The original r-cycle representative object
maps epimorphically onto cycles of the left interval
D^(1-(q+1))/D^(1-(q-r+2)), by the left-interval representative theorem.
Its class followed by the quotient map to the right interval is c_r: cancel
the target cycle inclusion and use the defining equations of the two lifts.
The spectral page is a quotient of left-interval cohomology and embeds into
right-interval cohomology. The composite is the endpoint-square map: expand
cokernelSequenceE.g and kernelSequenceE.f, use the identities for πE followed
by ιE, toCycles followed by iCycles, and pOpcycles followed by fromOpcycles.
The interval-square naturality theorem identifies this with the quotient map
on cohomology. Since the maps onto left-interval cycles, onto its homology,
and onto the spectral page are epic, the two composite image subobjects agree.
The last embedding is monic, so its image is its own subobject. At r=2 the
left and right intervals coincide; c_r is epic and the first-page embedding
is an isomorphism, hence both subobjects are top. No finite-filtration or
boundedness assumption enters. -/
theorem filteredComplex_decalage_page_image
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    imageSubobject (filteredComplexDecalageRepresentativeClass U p q r hr) =
      Subobject.mk (filteredComplexDecalagePageEmbedding U p q r hr) := by
  by_cases hr₂ : r = 2
  · subst r
    have hi := representative_image_of_left_interval U p q 2 le_rfl
      (1 - (q + (2 - 1))) (1 - q) (by omega) (by omega) (by omega) le_rfl
      (𝟙 _) (by simp)
    have he : IsIso (filteredComplexDecalagePageEmbedding U p q 2 le_rfl) := by
      rw [filteredComplexDecalagePageEmbedding_two]
      infer_instance
    rw [hi, HomologicalComplex.homologyMap_id, imageSubobject_mono,
      Subobject.mk_eq_top_of_isIso, Subobject.mk_eq_top_of_isIso]
  · let X := (filteredComplexDecalageSpectralObjectFunctor C).obj U
    let i₀ : EInt := (q - r + 2 : ℤ)
    let i₁ : EInt := q
    let i₂ : EInt := (q + 1 : ℤ)
    let i₃ : EInt := (q + (r - 1) : ℤ)
    let f₁ : i₀ ⟶ i₁ := homOfLE (by dsimp [i₀, i₁]; simp; omega)
    let f₂ : i₁ ⟶ i₂ := homOfLE (by dsimp [i₁, i₂]; simp)
    let f₃ : i₂ ⟶ i₃ := homOfLE (by dsimp [i₂, i₃]; simp; omega)
    let f₁₂ : i₀ ⟶ i₂ := homOfLE (by dsimp [i₀, i₂]; simp; omega)
    let f₂₃ : i₁ ⟶ i₃ := homOfLE (by dsimp [i₁, i₃]; simp; omega)
    let S := X.cokernelSequenceE f₁ f₂ f₃ f₁₂ (Subsingleton.elim _ _)
      (p + q - 1) (p + q) (p + q + 1)
    let K := X.kernelSequenceE f₁ f₂ f₃ f₂₃ (Subsingleton.elim _ _)
      (p + q - 1) (p + q) (p + q + 1)
    let e := X.spectralSequencePageXIso Abelian.SpectralObject.coreE₂Cohomological r hr
      (p, q) i₀ i₁ i₂ i₃ rfl rfl rfl (by dsimp [i₃]; congr 1; omega)
      (p + q - 1) (p + q) (p + q + 1) rfl
    let β := ComposableArrows.homMk₁ (F := ComposableArrows.mk₁ f₁₂)
      (G := ComposableArrows.mk₁ f₂₃) f₁ f₃ (Subsingleton.elim _ _)
    let T := filteredComplexDecalageIntervalHom U (leOfHom f₁₂) (leOfHom f₂₃) β
    let I := filteredComplexDecalageIntervalIso U i₀ i₂ (leOfHom f₁₂) (p + q)
    let J := filteredComplexDecalageIntervalIso U i₁ i₃ (leOfHom f₂₃) (p + q)
    let D := U.filtration.decalage
    let a := 1 - (q + 1)
    let b := 1 - (q - r + 2)
    let a' := 1 - (q + (r - 1))
    let f : D.complexQuotient a b (by dsimp [a, b]; omega) ⟶
        D.complexQuotient a' (1 - q) (by dsimp [a']; omega) := T.τ₃
    have hf : D.complexQuotientπ a b (by dsimp [a, b]; omega) ≫ f =
        Subobject.ofLE (D.step a) (D.step a')
          (D.antitone_step (by dsimp [a, a']; omega)) ≫
        D.complexQuotientπ a' (1 - q) (by dsimp [a']; omega) := T.comm₂₃.symm
    have hi := representative_image_of_left_interval U p q r hr a b
      (by dsimp [a]; omega) (by dsimp [b]; omega)
      (by dsimp [a, b]; omega) (by dsimp [a, a']; omega) f hf
    let s := I.inv ≫ S.g ≫ e.inv
    have hs : s ≫ filteredComplexDecalagePageEmbedding U p q r hr =
        HomologicalComplex.homologyMap f (p + q) := by
      unfold filteredComplexDecalagePageEmbedding
      rw [dif_neg hr₂]
      change (I.inv ≫ S.g ≫ e.inv) ≫ (e.hom ≫ K.f ≫ J.hom) = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% (spectral_page_image_factor X f₁ f₂ f₃ f₁₂ f₂₃ (p + q))]
      rw [filteredComplexDecalageIntervalIso_map]
      change I.inv ≫ I.hom ≫ HomologicalComplex.homologyMap f (p + q) = _
      rw [← Category.assoc]
      simp only [Iso.inv_hom_id, Category.id_comp]
    have : Epi s := by dsimp [s]; infer_instance
    calc
      imageSubobject (filteredComplexDecalageRepresentativeClass U p q r hr) =
          imageSubobject (HomologicalComplex.homologyMap f (p + q)) := hi
      _ = imageSubobject (s ≫ filteredComplexDecalagePageEmbedding U p q r hr) := by
        congr 1
        exact hs.symm
      _ = imageSubobject (filteredComplexDecalagePageEmbedding U p q r hr) :=
        imageSubobject_comp_of_epi _ _
      _ = Subobject.mk (filteredComplexDecalagePageEmbedding U p q r hr) :=
        imageSubobject_mono _

end CategoryTheory
