/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalageTower
public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
import Sheaf.CategoryTheory.CartanEilenbergSmartTruncationSpectralObject

/-! Existence part of the CE decalage spectral object comparison.
Source: Stacks Project, Tags 015X and 015K.
(blueprint: lem-sp-ce-decalage-spectral-object-iso-exists).
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem mapped_firstQuadrant
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {F : A ⥤ B} [F.Additive] (G : B ⥤ C) [G.Additive]
    (P : CartanEilenbergPresentation F) (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).X i).X j) := by
  rcases h with hi | hj
  · exact (HomologicalComplex.eval C (.up ℤ) j).map_isZero
      ((G.mapHomologicalComplex (.up ℕ) ⋙ ComplexShape.embeddingUpNat.extendFunctor C).map_isZero
        (P.zero_neg i hi))
  · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat j
      (fun m hm ↦ by change (m : ℤ) = j at hm; omega)

/-- A natural comparison morphism, known to be invertible only on intervals starting at
minus infinity.
Source: Stacks Project, Tag 015X, Remark 13.26.15; Tag 015K, Remark 13.21.4.
(blueprint: lem-sp-ce-decalage-spectral-object-iso-exists).

Proof. At finite cutoff b, identify the decalage step with the total of the horizontal
smart truncation at b-1. The CE augmentation gives a quasi-isomorphism from the
truncation of F(J) into a bounded-below complex of injectives. Compare its mapped
resolution with RG of that truncation using the inverse derived unit. The unique
augmentation square commutes for cutoff inclusions and for presentation maps. At
minus infinity use zero; at plus infinity use the full CE resolution. For interval
morphisms compare their mapping-cone triangles with the truncation triangles, using
the normalized first two maps and t-structure orthogonality to fix the third map.
The resulting comparison morphism commutes with the connecting arrows. Apply
cohomology to these triangle squares. For bottom intervals its map is invertible:
it is the composite of the resolution comparison, the cochain/derived truncation
comparison, and the resolution identification of F(J) with RF(X). The normalized
augmentation squares give presentation naturality, and cancellation of the monic
step inclusions extends it to every filtered lift of the specified total map.
No invertibility on general interval cohomology is claimed here; that follows
separately by the five lemma. -/
theorem cartanEilenberg_decalage_spectralObject_iso_exists
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
    (hL : ∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
      (L P).complexStep p n =
        ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) :
    ∃ e : ∀ P : CartanEilenbergPresentation F,
      (filteredComplexDecalageSpectralObjectFunctor C).obj
          (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
        F.grothendieckSpectralObject G P.X,
      (∀ (P : CartanEilenbergPresentation F) (n : ℤ) (b : EInt),
        IsIso (((e P).hom n).app (ComposableArrows.mk₁
          (homOfLE (bot_le : (⊥ : EInt) ≤ b))))) ∧
      ∀ (P Q : CartanEilenbergPresentation F) (d : P.Comparison Q)
        (t : (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
          (⟨Q.total G, L Q⟩ : FilteredObject (CochainComplex C ℤ))),
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ) →
        (filteredComplexDecalageSpectralObjectFunctor C).map t ≫ e Q =
          e P ≫ (F.grothendieckSpectralObjectFunctor G).map d.f := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    obtain ⟨c, hc, hn⟩ := cartanEilenberg_smartTruncation_spectralObject_comparison F G
    let s (P : CartanEilenbergPresentation F) :
        (cochainTowerSpectralObjectFunctor C).obj
            (CartanEilenbergPresentation.mappedSmartTruncationTower G P.I) ≅
          (filteredComplexDecalageSpectralObjectFunctor C).obj
            (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) :=
      (cochainTowerSpectralObjectFunctor C).mapIso
          (CartanEilenbergPresentation.mappedSmartTruncationTowerIso G P.I) ≪≫
        HomologicalComplex₂.smartTruncationDecalageSpectralObjectIso
          ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
          (mapped_firstQuadrant G P) (L P) (hL P)
    let r (P : CartanEilenbergPresentation F) :
        F.grothendieckSpectralObject G P.X ≅
          (derivedTruncationSpectralObjectFunctor G).obj
            (DerivedCategory.Plus.Q.obj (F.specifiedResolutionComplex P.J)) :=
      (derivedTruncationSpectralObjectFunctor G).mapIso
        (F.specifiedResolutionDerivedSingleIso P.J)
    refine ⟨fun P ↦ (s P).inv ≫ c P ≫ (r P).inv, ?_, ?_⟩
    · intro P n b
      have := hc P n b
      change IsIso (((((s P).inv ≫ c P ≫ (r P).inv).hom n)).app _)
      simp only [Abelian.SpectralObject.comp_hom, NatTrans.comp_app]
      let D := ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ b))
      have : IsIso ((((s P).inv).hom n).app D) :=
        inferInstanceAs (IsIso ((Abelian.SpectralObject.hFunctor n D).map (s P).inv))
      have : IsIso ((((r P).inv).hom n).app D) :=
        inferInstanceAs (IsIso ((Abelian.SpectralObject.hFunctor n D).map (r P).inv))
      infer_instance
    · intro P Q d t ht
      let φ : P.J.Hom Q.J d.f :=
        ⟨d.β, by simpa only [CochainComplex.single₀_map_f_zero] using d.comm_ι⟩
      have hr := (derivedTruncationSpectralObjectFunctor G).congr_map
        (F.specifiedResolutionDerivedSingleIso_naturality P.J Q.J φ)
      simp only [CategoryTheory.Functor.map_comp] at hr
      have h₁ := (cochainTowerSpectralObjectFunctor C).congr_map
        (CartanEilenbergPresentation.mappedSmartTruncationTowerIso_naturality G d.α)
      have h₂ := (cochainTowerSpectralObjectFunctor C).congr_map
        (HomologicalComplex₂.smartTruncationDecalageTowerIso_naturality
          ((CartanEilenbergPresentation.mappedFunctor G).map d.α)
          (mapped_firstQuadrant G P) (mapped_firstQuadrant G Q)
          (L P) (L Q) (hL P) (hL Q) t ht)
      simp only [CategoryTheory.Functor.map_comp] at h₁ h₂
      have hs : (cochainTowerSpectralObjectFunctor C).map
            (CartanEilenbergPresentation.mappedSmartTruncationTowerMap G d.α) ≫
            (s Q).hom = (s P).hom ≫
              (filteredComplexDecalageSpectralObjectFunctor C).map t := by
        dsimp only [s, Iso.trans_hom,
          HomologicalComplex₂.smartTruncationDecalageSpectralObjectIso, Functor.mapIso_hom]
        rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
        rfl
      have hs' : (filteredComplexDecalageSpectralObjectFunctor C).map t ≫ (s Q).inv =
          (s P).inv ≫ (cochainTowerSpectralObjectFunctor C).map
            (CartanEilenbergPresentation.mappedSmartTruncationTowerMap G d.α) := by
        apply (Iso.comp_inv_eq (s Q)).2
        rw [Category.assoc]
        apply (Iso.eq_inv_comp (s P)).2
        exact hs.symm
      let k := (derivedTruncationSpectralObjectFunctor G).map
        (DerivedCategory.Plus.Q.map (ObjectProperty.homMk
          ((F.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.extendMap d.β ComplexShape.embeddingUpNat)) :
          F.specifiedResolutionComplex P.J ⟶ F.specifiedResolutionComplex Q.J))
      have hr₀ : (F.grothendieckSpectralObjectFunctor G).map d.f ≫ (r Q).hom =
          (r P).hom ≫ k := by exact hr
      have hr' : k ≫ (r Q).inv =
          (r P).inv ≫ (F.grothendieckSpectralObjectFunctor G).map d.f := by
        apply (Iso.comp_inv_eq (r Q)).2
        rw [Category.assoc]
        apply (Iso.eq_inv_comp (r P)).2
        exact hr₀.symm
      let u := (cochainTowerSpectralObjectFunctor C).map
        (CartanEilenbergPresentation.mappedSmartTruncationTowerMap G d.α)
      let m := (filteredComplexDecalageSpectralObjectFunctor C).map t
      change m ≫ ((s Q).inv ≫ c Q ≫ (r Q).inv) =
        ((s P).inv ≫ c P ≫ (r P).inv) ≫ _
      calc
        m ≫ ((s Q).inv ≫ c Q ≫ (r Q).inv) =
            ((m ≫ (s Q).inv) ≫ c Q) ≫ (r Q).inv := by simp only [Category.assoc]
        _ = (((s P).inv ≫ u) ≫ c Q) ≫ (r Q).inv := by rw [hs']
        _ = ((s P).inv ≫ (u ≫ c Q)) ≫ (r Q).inv := by simp only [Category.assoc]
        _ = ((s P).inv ≫ (c P ≫ k)) ≫ (r Q).inv := by rw [hn P Q d]
        _ = ((s P).inv ≫ c P) ≫ (k ≫ (r Q).inv) := by simp only [Category.assoc]
        _ = ((s P).inv ≫ c P) ≫ ((r P).inv ≫ _) := by rw [hr']
        _ = _ := by simp only [Category.assoc]
end CategoryTheory
