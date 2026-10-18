/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! # Existence of the page-two map

Source: Mathlib Algebra/Homology/SpectralObject/{Page,SpectralSequence,FirstPage}.lean,
Stacks Project Tags 012K and 015K (blueprint: lem-sp-spectral-object-page-two-map-extension).
(blueprint: lem-sp-spectral-object-page-two-map-existence)

Proof: construct the page components by applying the homology-map construction to the
three-term complexes defining each page object. Naturality of the connecting morphisms
proves compatibility with page differentials; the kernel and image universal properties
prove compatibility with successor-page homology isomorphisms and the displayed page-two
comparison equation.
-/

@[expose] public section

universe uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

private def shortComplexHom
    {C ι : Type*} [Category* C] [Preorder ι] [Abelian C]
    {X Y : SpectralObject C ι} (φ : X ⟶ Y)
    {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶
      Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ where
  τ₁ := (φ.hom n₀).app (ComposableArrows.mk₁ f₃)
  τ₂ := (φ.hom n₁).app (ComposableArrows.mk₁ f₂)
  τ₃ := (φ.hom n₂).app (ComposableArrows.mk₁ f₁)
  comm₁₂ := (φ.comm n₀ n₁ hn₁ f₂ f₃).symm
  comm₂₃ := (φ.comm n₁ n₂ hn₂ f₁ f₂).symm

private noncomputable def EHom
    {C ι : Type*} [Category* C] [Preorder ι] [Abelian C]
    {X Y : SpectralObject C ι} (φ : X ⟶ Y)
    {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.homologyMap (shortComplexHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

section

variable {C ι : Type*} [Category* C] [Preorder ι] [Abelian C]
  {X Y : SpectralObject C ι} (φ : X ⟶ Y)

private noncomputable def cyclesHom
    {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (n : ℤ) :
    X.cycles f₁ f₂ n ⟶ Y.cycles f₁ f₂ n :=
  Y.liftCycles f₁ f₂ n (n + 1) rfl
    (X.iCycles f₁ f₂ n ≫ (φ.hom n).app (ComposableArrows.mk₁ f₂)) (by
      rw [Category.assoc, ← φ.comm n (n + 1) rfl f₁ f₂, ← Category.assoc]
      simp)

@[reassoc (attr := simp)]
private lemma cyclesHom_i
    {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (n : ℤ) :
    cyclesHom φ f₁ f₂ n ≫ Y.iCycles f₁ f₂ n =
      X.iCycles f₁ f₂ n ≫ (φ.hom n).app (ComposableArrows.mk₁ f₂) := by
  apply liftCycles_i

@[reassoc]
private lemma toCycles_cyclesHom
    {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (n : ℤ) :
    X.toCycles f₁ f₂ (f₁ ≫ f₂) rfl n ≫ cyclesHom φ f₁ f₂ n =
      (φ.hom n).app (ComposableArrows.mk₁ (f₁ ≫ f₂)) ≫
        Y.toCycles f₁ f₂ (f₁ ≫ f₂) rfl n := by
  rw [← cancel_mono (Y.iCycles f₁ f₂ n)]
  simp only [Category.assoc, cyclesHom_i, toCycles_i_assoc, toCycles_i]
  exact (φ.hom n).naturality _

@[reassoc]
private lemma πE_EHom
    {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ EHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      cyclesHom φ f₁ f₂ n₁ ≫ Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  have h : (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      ShortComplex.cyclesMap (shortComplexHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) =
      cyclesHom φ f₁ f₂ n₁ ≫ (Y.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv := by
    rw [← cancel_mono (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles]
    simp only [Category.assoc, ShortComplex.cyclesMap_i,
      cyclesIso_inv_i, cyclesIso_inv_i_assoc, cyclesHom_i]
    rfl
  simp only [πE, EHom, Category.assoc, ShortComplex.homologyπ_naturality]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyπ) h

@[reassoc]
private lemma EHom_map
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : ComposableArrows.mk₃ f₁ f₂ f₃ ⟶ ComposableArrows.mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    EHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ =
      X.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ ≫
        EHom φ g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [EHom, map]
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  ext <;> dsimp [shortComplexHom, shortComplexMap]
  all_goals exact ((φ.hom _).naturality _).symm

@[reassoc]
private lemma EHom_d
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (hn₃ : n₂ + 1 = n₃) :
    EHom φ f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ =
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
        EHom φ f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ := by
  rw [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_epi (X.toCycles f₃ f₄ (f₃ ≫ f₄) rfl n₁)]
  rw [πE_EHom_assoc, toCycles_cyclesHom_assoc,
    Y.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₀ n₁ n₂ n₃,
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₀ n₁ n₂ n₃,
    πE_EHom, toCycles_cyclesHom_assoc]
  rw [← φ.comm_assoc n₁ n₂ hn₂ (f₁ ≫ f₂) (f₃ ≫ f₄)]

private lemma EHom_EIsoH
    {i j : ι} (f : i ⟶ j) (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    EHom φ (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≫ (Y.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (φ.hom n₁).app (ComposableArrows.mk₁ f) := by
  exact (ShortComplex.HomologyMapData.ofZeros
    (shortComplexHom φ (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂)
    (X.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (X.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂)
    (Y.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (Y.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂)).left.homologyMap_comm

section Pages

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)

private noncomputable def pageXHom (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    SpectralSequence.pageX X data r pq hr ⟶ SpectralSequence.pageX Y data r pq hr :=
  EHom φ (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq)) (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
    (by omega) rfl

@[reassoc]
private lemma pageXHom_iso (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    pageXHom φ data r hr pq ≫
        (SpectralSequence.pageXIso Y data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
          n₀ n₁ n₂ h hn₁ hn₂).hom =
      (SpectralSequence.pageXIso X data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
          n₀ n₁ n₂ h hn₁ hn₂).hom ≫
        EHom φ (homOfLE (data.le₀₁' r hr pq h₀ h₁))
          (homOfLE (data.le₁₂' pq h₁ h₂)) (homOfLE (data.le₂₃' r hr pq h₂ h₃))
          n₀ n₁ n₂ hn₁ hn₂ := by
  subst h₀ h₁ h₂ h₃ h
  obtain rfl : n₀ = data.deg pq - 1 := by omega
  obtain rfl : n₂ = data.deg pq + 1 := by omega
  simp [SpectralSequence.pageXIso, pageXHom]

private noncomputable def pageHom (r : ℤ) (hr : r₀ ≤ r) :
    SpectralSequence.page X data r hr ⟶ SpectralSequence.page Y data r hr where
  f pq := pageXHom φ data r hr pq
  comm' pq pq' h := by
    change pageXHom φ data r hr pq ≫ SpectralSequence.pageD Y data r pq pq' hr =
      SpectralSequence.pageD X data r pq pq' hr ≫ pageXHom φ data r hr pq'
    classical
    dsimp only [SpectralSequence.pageD]
    rw [dif_pos h, dif_pos h, ← Category.assoc, Iso.comp_inv_eq,
      Category.assoc, pageXHom_iso]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact EHom_d φ _ _ _ _ _ _ _ _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma pageHom_homology
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    HomologicalComplex.homologyMap (pageHom φ data r hr) pq ≫
        (SpectralSequence.homologyIso Y data r r' hrr' hr pq).hom =
      (SpectralSequence.homologyIso X data r r' hrr' hr pq).hom ≫
        pageXHom φ data r' (by omega) pq := by
  let DX := SpectralSequence.homologyData X data r r' hrr' hr
    ((c r).prev pq) pq ((c r).next pq) rfl rfl
    (data.i₀ r' pq) (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq)
    (data.i₃ r pq) (data.i₃ r' pq) rfl rfl rfl rfl rfl rfl
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
  let DY := SpectralSequence.homologyData Y data r r' hrr' hr
    ((c r).prev pq) pq ((c r).next pq) rfl rfl
    (data.i₀ r' pq) (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq)
    (data.i₃ r pq) (data.i₃ r' pq) rfl rfl rfl rfl rfl rfl
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl
  let k : DX.left.K ⟶ DY.left.K :=
    EHom φ (homOfLE (data.le₀₁ r' pq)) (homOfLE (data.le₁₂ pq))
      (homOfLE (data.le₂₃ r pq)) (data.deg pq - 1) (data.deg pq)
      (data.deg pq + 1) (by omega) rfl
  let ψ := (HomologicalComplex.shortComplexFunctor _ _ pq).map (pageHom φ data r hr)
  have hi : k ≫ DY.left.i = DX.left.i ≫ ψ.τ₂ := by
    change EHom φ _ _ _ _ _ _ _ _ ≫
        (Y.mapFourδ₁Toδ₀' _ _ _ _ _ _ _ _ _ _ _ _) ≫ _ =
      (X.mapFourδ₁Toδ₀' _ _ _ _ _ _ _ _ _ _ _ _ ≫ _) ≫ _
    simp only [SpectralSequence.pageXIso, eqToIso_refl, Iso.refl_inv]
    erw [Category.comp_id, Category.comp_id]
    exact EHom_map φ _ _ _ _ _ _ _ _ _ _ _ _
  have hp : DX.left.π ≫ pageXHom φ data r' (by omega) pq = k ≫ DY.left.π := by
    change X.mapFourδ₄Toδ₃' _ _ _ _ _ _ _ _ _ _ _ _ ≫ _ =
      _ ≫ Y.mapFourδ₄Toδ₃' _ _ _ _ _ _ _ _ _ _ _ _
    exact (EHom_map φ _ _ _ _ _ _ _ _ _ _ _ _).symm
  let γ : ShortComplex.LeftHomologyMapData ψ DX.left DY.left :=
    { φK := k
      φH := pageXHom φ data r' (by omega) pq
      commi := hi
      commf' := by
        rw [← cancel_mono DY.left.i, Category.assoc, hi,
          ShortComplex.LeftHomologyData.f'_i_assoc, Category.assoc,
          ShortComplex.LeftHomologyData.f'_i, ψ.comm₁₂]
      commπ := hp }
  simp only [SpectralSequence.homologyIso, SpectralSequence.homologyIso',
    Iso.trans_hom, Iso.symm_hom, SpectralSequence.pageXIso, eqToIso_refl,
    Iso.refl_inv]
  erw [Category.comp_id, Category.comp_id]
  exact γ.homologyMap_comm

unseal spectralSequence in
private noncomputable def spectralSequenceHom
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data] :
    X.spectralSequence data ⟶ Y.spectralSequence data where
  hom r hr := pageHom φ data r hr
  comm r r' pq hrr' hr := pageHom_homology φ data r r' hrr' hr pq

unseal spectralSequence in
private lemma spectralSequenceHom_firstPage
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    [data.HasFirstPageComputation] (pq : κ) :
    ((spectralSequenceHom φ data).hom r₀).f pq ≫
        (Y.spectralSequenceFirstPageXIso data pq _ _ rfl rfl _ rfl).hom =
      (X.spectralSequenceFirstPageXIso data pq _ _ rfl rfl _ rfl).hom ≫
        (φ.hom (data.deg pq)).app (ComposableArrows.mk₁ (homOfLE (data.le₁₂ pq))) := by
  dsimp only [spectralSequenceHom, pageHom]
  rw [Y.spectralSequenceFirstPageXIso_hom data pq _ _ rfl rfl
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl,
    X.spectralSequenceFirstPageXIso_hom data pq _ _ rfl rfl
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl]
  change pageXHom φ data r₀ (by rfl) pq ≫
      (SpectralSequence.pageXIso Y data r₀ (by rfl) pq _ _ _ _
        _ rfl rfl _ _ _ _ rfl).hom ≫ _ =
    ((SpectralSequence.pageXIso X data r₀ (by rfl) pq _ _ _ _
        _ rfl rfl _ _ _ _ rfl).hom ≫ _) ≫ _
  rw [pageXHom_iso_assoc]
  simp only [Category.assoc]
  congr 1
  exact EHom_EIsoH φ _ _ _ _ _ _

end Pages

end

/-- A morphism of spectral objects induces a morphism of their canonical `E₂` spectral
sequences satisfying the page-two comparison equation. The construction uses the
kernel/image maps on the three-term complexes defining `pageX`; the compatibility
of connecting morphisms gives the differential and successor-page equations.
Source: Mathlib Algebra/Homology/SpectralObject/{Page,SpectralSequence,FirstPage}.lean,
Stacks Project Tags 012K and 015K (blueprint: lem-sp-spectral-object-page-two-map-extension).
(blueprint: lem-sp-spectral-object-page-two-map-existence)

Proof: construct the page components by applying the homology-map construction to the
three-term complexes defining each page object. Naturality of the connecting morphisms
proves compatibility with page differentials; the kernel and image universal properties
prove compatibility with successor-page homology isomorphisms and the displayed page-two
comparison equation.
-/
theorem exists_pageTwoMap_data
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {X Y : SpectralObject C EInt} (φ : X ⟶ Y) :
    ∃ e : X.E₂SpectralSequence ⟶ Y.E₂SpectralSequence,
      ∀ (p q : ℤ),
        (e.hom 2).f (p, q) ≫
            ((HomologicalComplex.eval C _ (p, q)).mapIso
              ((SpectralSequence.pageFunctor C _ 2 2).mapIso (Iso.refl _)) ≪≫
            Y.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl
              (p + q) rfl).hom =
          ((HomologicalComplex.eval C _ (p, q)).mapIso
              ((SpectralSequence.pageFunctor C _ 2 2).mapIso (Iso.refl _)) ≪≫
            X.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl
              (p + q) rfl).hom ≫
            (φ.hom (p + q)).app (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by
  refine ⟨spectralSequenceHom φ coreE₂Cohomological, ?_⟩
  intro p q
  convert spectralSequenceHom_firstPage φ coreE₂Cohomological (p, q) using 1 <;>
    simp [E₂SpectralSequence, coreE₂Cohomological]

end CategoryTheory.Abelian.SpectralObject
