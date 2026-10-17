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

universe uC vC uI vI

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

section MorphismPages

open Category Limits ComposableArrows

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {ι : Type uI} [Category.{vI} ι] {X Y : SpectralObject C ι}

namespace Hom

variable (φ : X ⟶ Y)

section
variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by omega)
  (hn₂ : n₁ + 1 = n₂ := by omega)

/-- The map of three-term complexes induced by a spectral-object morphism. -/
private def shortComplexHom : X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶
    Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ where
  τ₁ := (φ.hom n₀).app (mk₁ f₃)
  τ₂ := (φ.hom n₁).app (mk₁ f₂)
  τ₃ := (φ.hom n₂).app (mk₁ f₁)
  comm₁₂ := (φ.comm n₀ n₁ hn₁ f₂ f₃).symm
  comm₂₃ := (φ.comm n₁ n₂ hn₂ f₁ f₂).symm

/-- The induced map between the objects used on the pages. -/
private noncomputable def eMap : X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶
    Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.homologyMap (shortComplexHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

end

section
variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

/-- The induced map on cycles. -/
private noncomputable def cMap : X.cycles f g n ⟶ Y.cycles f g n :=
  Y.liftCycles f g n (n + 1) rfl
    (X.iCycles f g n ≫ (φ.hom n).app (mk₁ g)) (by
      rw [assoc, ← φ.comm, X.iCycles_δ_assoc f g n (n + 1) rfl, zero_comp])

@[reassoc]
private lemma cMap_i : cMap φ f g n ≫ Y.iCycles f g n =
    X.iCycles f g n ≫ (φ.hom n).app (mk₁ g) := by
  apply liftCycles_i

/-- The induced map on opcycles. -/
private noncomputable def oMap : X.opcycles f g n ⟶ Y.opcycles f g n :=
  X.descOpcycles f g (n - 1) n (by omega)
    ((φ.hom n).app (mk₁ f) ≫ Y.pOpcycles f g n) (by
      rw [← assoc, φ.comm, assoc, Y.δ_pOpcycles f g (n - 1) n (by omega), comp_zero])

@[reassoc]
private lemma p_oMap : X.pOpcycles f g n ≫ oMap φ f g n =
    (φ.hom n).app (mk₁ f) ≫ Y.pOpcycles f g n := by
  apply p_descOpcycles

end

section
variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by omega)
  (hn₂ : n₁ + 1 = n₂ := by omega)

@[reassoc]
private lemma π_eMap : X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
    eMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      cMap φ f₁ f₂ n₁ ≫ Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [eMap, πE]
  rw [assoc, ShortComplex.homologyπ_naturality]
  simp only [← assoc]
  congr 1
  apply (cancel_mono (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles).1
  simp only [assoc, ShortComplex.cyclesMap_i, shortComplexHom,
    cyclesIso_inv_i, cyclesIso_inv_i_assoc, cMap_i]

@[reassoc]
private lemma eMap_ι : eMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
    Y.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ oMap φ f₂ f₃ n₁ := by
  dsimp only [eMap, ιE]
  rw [← assoc, ShortComplex.homologyι_naturality, assoc]
  simp only [assoc]
  congr 1
  apply (cancel_epi (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles).1
  simp only [ShortComplex.p_opcyclesMap_assoc, shortComplexHom,
    p_opcyclesIso_hom, p_opcyclesIso_hom_assoc, p_oMap]

end

section
variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (hfg : f ≫ g = fg) (n : ℤ)

@[reassoc]
private lemma toCycles_cMap : X.toCycles f g fg hfg n ≫ cMap φ f g n =
    (φ.hom n).app (mk₁ fg) ≫ Y.toCycles f g fg hfg n := by
  apply (cancel_mono (Y.iCycles f g n)).1
  simp only [assoc, cMap_i, toCycles_i_assoc, toCycles_i]
  exact (φ.hom n).naturality (twoδ₁Toδ₀ f g fg hfg)


end

section
variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by omega)

@[reassoc]
private lemma cMap_Ψ : cMap φ f₂ f₃ n₀ ≫ Y.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ =
    X.Ψ f₁ f₂ f₃ n₀ n₁ hn₁ ≫ oMap φ f₁ f₂ n₁ := by
  apply (cancel_epi (X.toCycles f₂ f₃ (f₂ ≫ f₃) rfl n₀)).1
  rw [← assoc, toCycles_cMap, assoc,
    Y.toCycles_Ψ f₁ f₂ f₃ (f₂ ≫ f₃) rfl n₀ n₁ hn₁,
    X.toCycles_Ψ_assoc f₁ f₂ f₃ (f₂ ≫ f₃) rfl n₀ n₁ hn₁, p_oMap,
    ← φ.comm_assoc]

end

section
variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (n₀ n₁ n₂ n₃ : ℤ)
  (hn₁ : n₀ + 1 = n₁ := by omega) (hn₂ : n₁ + 1 = n₂ := by omega)
  (hn₃ : n₂ + 1 = n₃ := by omega)

@[reassoc]
private lemma eMap_d : eMap φ f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫
    Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ =
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
        eMap φ f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ := by
  apply (cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂)).1
  apply (cancel_mono (Y.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃)).1
  simp only [assoc, π_eMap_assoc, eMap_ι, πE_d_ιE, πE_d_ιE_assoc,
    cMap_Ψ]

end

section
variable {i j k l i' j' k' l' : ι}
  (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by omega)
  (hn₂ : n₁ + 1 = n₂ := by omega)

@[reassoc]
private lemma eMap_map : eMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
    Y.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ =
      X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
        eMap φ f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [eMap, SpectralObject.map]
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  ext
  · exact ((φ.hom n₀).naturality _).symm
  · exact ((φ.hom n₁).naturality _).symm
  · exact ((φ.hom n₂).naturality _).symm

end

section
variable {i j : ι} (f : i ⟶ j)
  (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by omega)
  (hn₂ : n₁ + 1 = n₂ := by omega)

@[reassoc]
private lemma eMap_EIsoH : eMap φ (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≫
    (Y.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (φ.hom n₁).app (mk₁ f) := by
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (shortComplexHom φ (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂)
    (X.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (X.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂)
    (Y.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (Y.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂)).homologyMap_comm

end

end Hom

end MorphismPages

section MorphismSpectralSequence

open Category Limits ComposableArrows

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {ι : Type uI} [Preorder ι] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {X Y : SpectralObject C ι} (φ : X ⟶ Y)
  (data : SpectralSequenceDataCore ι c r₀)

namespace Hom

/-- The morphism on the objects of a page. -/
private noncomputable def pageMap (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    SpectralSequence.pageX X data r pq hr ⟶ SpectralSequence.pageX Y data r pq hr :=
  eMap φ (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq)) (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
    (by omega) (by omega)

@[reassoc]
private lemma pageMap_pageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by omega) (hn₂ : n₁ + 1 = n₂ := by omega) :
    pageMap φ data r hr pq ≫
        (SpectralSequence.pageXIso Y data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
          n₀ n₁ n₂ h hn₁ hn₂).hom =
      (SpectralSequence.pageXIso X data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
        n₀ n₁ n₂ h hn₁ hn₂).hom ≫
        eMap φ (homOfLE (data.le₀₁' r hr pq h₀ h₁))
          (homOfLE (data.le₁₂' pq h₁ h₂)) (homOfLE (data.le₂₃' r hr pq h₂ h₃))
          n₀ n₁ n₂ hn₁ hn₂ := by
  obtain rfl : n₀ = n₁ - 1 := by omega
  obtain rfl : n₂ = n₁ + 1 := by omega
  subst h h₀ h₁ h₂ h₃
  simp [SpectralSequence.pageXIso, pageMap]

/-- The maps on a page commute with its differential. -/
private noncomputable def pageHom (r : ℤ) (hr : r₀ ≤ r) :
    SpectralSequence.page X data r hr ⟶ SpectralSequence.page Y data r hr where
  f := pageMap φ data r hr
  comm' pq pq' h := by
    dsimp only [SpectralSequence.page, SpectralSequence.pageD]
    rw [dif_pos h, dif_pos h]
    rw [← assoc]
    dsimp only [pageMap]
    rw [eMap_d φ _ _ _ _ _ (data.deg pq - 1) (data.deg pq)
      (data.deg pq + 1) (data.deg pq + 2) (by omega) rfl (by omega)]
    simp only [assoc]
    congr 1
    rw [Iso.comp_inv_eq, assoc, Iso.eq_inv_comp]
    exact (pageMap_pageXIso φ data r hr pq' _ _ _ _ rfl rfl
      (data.hc₀₂ r pq pq' h) (data.hc₁₃ r pq pq' h) _ _ _
      (data.hc r pq pq' h) rfl (by omega)).symm

section
variable [X.HasSpectralSequence data] [Y.HasSpectralSequence data]

/-- Canonical homology data for a page, using the unmodified indices. -/
private noncomputable def pageHomologyData (Z : SpectralObject C ι) [Z.HasSpectralSequence data]
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    ((SpectralSequence.page Z data r hr).sc pq).HomologyData := by
  exact SpectralSequence.homologyData Z data r r' hrr' hr _ pq _ rfl rfl
    (data.i₀ r' pq (by omega)) (data.i₀ r pq hr) (data.i₁ pq) (data.i₂ pq)
    (data.i₃ r pq hr) (data.i₃ r' pq (by omega)) rfl rfl rfl rfl rfl rfl
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl (by omega) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The induced map between the canonical homology data of the pages. -/
private noncomputable def pageHomologyMapData
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor C (c r) pq).map (pageHom φ data r hr))
      (pageHomologyData data X r r' hrr' hr pq).left
      (pageHomologyData data Y r r' hrr' hr pq).left := by
  let k : (pageHomologyData data X r r' hrr' hr pq).left.K ⟶
      (pageHomologyData data Y r r' hrr' hr pq).left.K :=
    eMap φ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by omega) rfl
  have hi : k ≫ (pageHomologyData data Y r r' hrr' hr pq).left.i =
      (pageHomologyData data X r r' hrr' hr pq).left.i ≫
        ((HomologicalComplex.shortComplexFunctor C (c r) pq).map
          (pageHom φ data r hr)).τ₂ := by
    change eMap φ _ _ _ _ _ _ _ _ ≫ (Y.map .. ≫ 𝟙 _) =
      (X.map .. ≫ 𝟙 _) ≫ eMap φ _ _ _ _ _ _ _ _
    simp only [comp_id]
    exact eMap_map φ _ _ _ _ _ _ _
      (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by omega) rfl
  refine {
    φK := k
    φH := pageMap φ data r' (by omega) pq
    commi := hi
    commf' := ?_
    commπ := ?_ }
  · apply (cancel_mono (pageHomologyData data Y r r' hrr' hr pq).left.i).1
    rw [assoc, hi, ← assoc, ShortComplex.LeftHomologyData.f'_i,
      assoc, ShortComplex.LeftHomologyData.f'_i,
      ((HomologicalComplex.shortComplexFunctor C (c r) pq).map
        (pageHom φ data r hr)).comm₁₂]
  · change X.map .. ≫ eMap φ _ _ _ _ _ _ _ _ = k ≫ Y.map ..
    exact (eMap_map φ _ _ _ _ _ _ _
      (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by omega) rfl).symm

@[reassoc]
private lemma pageHom_comm (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    HomologicalComplex.homologyMap (pageHom φ data r hr) pq ≫
        (SpectralSequence.homologyIso Y data r r' hrr' hr pq).hom =
      (SpectralSequence.homologyIso X data r r' hrr' hr pq).hom ≫
        pageMap φ data r' (by omega) pq := by
  have h := (pageHomologyMapData φ data r r' hrr' hr pq).homologyMap_comm
  change HomologicalComplex.homologyMap (pageHom φ data r hr) pq ≫
      (pageHomologyData data Y r r' hrr' hr pq).left.homologyIso.hom =
    (pageHomologyData data X r r' hrr' hr pq).left.homologyIso.hom ≫
      pageMap φ data r' (by omega) pq at h
  change _ ≫ ((pageHomologyData data Y r r' hrr' hr pq).left.homologyIso.hom ≫ 𝟙 _) =
    ((pageHomologyData data X r r' hrr' hr pq).left.homologyIso.hom ≫ 𝟙 _) ≫ _
  simpa only [comp_id] using h

unseal spectralSequence in
/-- The morphism between spectral sequences induced by a morphism of spectral objects. -/
private noncomputable def spectralSequenceHom :
    X.spectralSequence data ⟶ Y.spectralSequence data where
  hom r hr := pageHom φ data r hr
  comm r r' pq hrr' hr := pageHom_comm φ data r r' hrr' hr pq

unseal spectralSequence in
@[reassoc]
private lemma spectralSequenceHom_firstPage [data.HasFirstPageComputation]
    (pq : κ) (i₁ i₂ : ι) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    ((spectralSequenceHom φ data).hom r₀).f pq ≫
        (Y.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn).hom =
      (X.spectralSequenceFirstPageXIso data pq i₁ i₂ h₁ h₂ n hn).hom ≫
        (φ.hom n).app (mk₁ (homOfLE (data.le₁₂' pq h₁ h₂))) := by
  dsimp only [spectralSequenceHom, pageHom, spectralSequenceFirstPageXIso, Iso.trans_hom,
    spectralSequencePageXIso]
  rw [pageMap_pageXIso_assoc φ data r₀ (by rfl) pq _ _ _ _ _ h₁ h₂ _
    (n - 1) n (n + 1) hn (by omega) rfl]
  simp only [assoc]
  congr 1
  exact eMap_EIsoH φ (homOfLE (data.le₁₂' pq h₁ h₂))
    (n - 1) n (n + 1) (by omega) rfl

end

end Hom

end MorphismSpectralSequence

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
  refine ⟨Hom.spectralSequenceHom φ coreE₂Cohomological, ?_⟩
  intro p q
  simpa using Hom.spectralSequenceHom_firstPage φ coreE₂Cohomological
    (p, q) _ _ rfl rfl (p + q) rfl

end CategoryTheory.Abelian.SpectralObject
