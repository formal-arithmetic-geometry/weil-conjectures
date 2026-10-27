/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-! # Restricting a coefficient comparison along compatible sections

Source: orientation-charts Step 4, pullback-compositor coherence.
(blueprint: lem-trf-section-pullback-coefficient-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u uB
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] Etale.sheafMonoidalCategory
attribute [local implicit_reducible] Etale.sheafBraidedCategory
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize


attribute [local irreducible] leftDerivedUpperStarComp leftDerivedUpperStarCompSectionIso

private theorem inverse_square {C : Type*} [Category C] {X Y Z W : C}
    (u : X ⟶ Y) (s : Y ≅ Z) (t : X ≅ W) (v : W ≅ Z)
    (h : u ≫ s.hom = t.hom ≫ v.hom) :
    v.inv ≫ t.inv ≫ u = s.inv := by
  apply (cancel_mono s.hom).1
  simp only [Category.assoc, h, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

private theorem section_endpoint (R : Type uB)
    [Category.{u + 1} R] [Abelian R] [IsGrothendieckAbelian.{u + 1} R]
    [MonoidalCategory R] [MonoidalPreadditive R] [SymmetricCategory R] [MonoidalClosed R]
    [Abelian.HasFunctorialFlatResolution R]
    {T S S' B : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ B) (a' : T ⟶ S') (b' : S' ⟶ B)
    (c₁ c₂ : T ⟶ B) (h₁ : c₁ = a ≫ b) (h₁' : c₁ = a' ≫ b')
    (h₂ : c₂ = a ≫ b) (h₂' : c₂ = a' ≫ b')
    (K : DerivedCategory (Sheaf B.smallEtaleTopology R)) :
    (leftDerivedUpperStarComp R a b c₁ h₁).inv.app K ≫
        (leftDerivedUpperStarComp R a' b' c₁ h₁').hom.app K =
      (leftDerivedUpperStarComp R a b c₂ h₂).inv.app K ≫
        (leftDerivedUpperStarComp R a' b' c₂ h₂').hom.app K := by
  obtain rfl : c₁ = c₂ := h₁.trans h₂.symm
  rfl

private theorem sectionCoefficient_square (R : Type uB)
    [Category.{u + 1} R] [Abelian R] [IsGrothendieckAbelian.{u + 1} R]
    [MonoidalCategory R] [MonoidalPreadditive R] [SymmetricCategory R] [MonoidalClosed R]
    [Abelian.HasFunctorialFlatResolution R]
    {B B' P P' : Scheme.{u}} (v : B' ⟶ B) (p : P ⟶ B) (q : P' ⟶ B')
    (h : P' ⟶ P) (z : B ⟶ P) (w : B' ⟶ P')
    (hp : h ≫ p = q ≫ v) (hz : w ≫ h = v ≫ z)
    (h₀ : z ≫ p = 𝟙 B) (h₁ : w ≫ q = 𝟙 B')
    (K : DerivedCategory (Sheaf B.smallEtaleTopology R)) :
    ((upperStar R v).leftDerivedFunctor).map
        ((leftDerivedUpperStarCompSectionIso R z p h₀).inv.app K) ≫
      ((leftDerivedUpperStarComp R v z).inv.app _ ≫
        (leftDerivedUpperStarComp R w h (v ≫ z) hz.symm).hom.app _) ≫
      ((upperStar R w).leftDerivedFunctor).map
        ((leftDerivedUpperStarComp R h p).inv.app K ≫
          (leftDerivedUpperStarComp R q v (h ≫ p) hp).hom.app K) =
      (leftDerivedUpperStarCompSectionIso R w q h₁).inv.app _ := by
  have H := leftDerivedUpperStar_map_comp_compSectionIso R v p q h z w hp hz h₀ h₁ K
  have hi := inverse_square _
    ((leftDerivedUpperStarCompSectionIso R w q h₁).app _)
    (((leftDerivedUpperStarComp R w h).symm ≪≫
      leftDerivedUpperStarComp R v z (w ≫ h) hz).app _)
    (((upperStar R v).leftDerivedFunctor).mapIso
      ((leftDerivedUpperStarCompSectionIso R z p h₀).app K)) H
  simp only [Functor.mapIso_inv, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app] at hi
  have he := section_endpoint R v z w h
    (v ≫ z) (w ≫ h) rfl hz.symm hz rfl
    (((upperStar R p).leftDerivedFunctor).obj K)
  simpa only [Category.assoc, he] using hi


/-- A square on ambient coefficients remains a square after restriction to sections.
Source: orientation-charts Step 4; parent finite-ring section deformation proof Step 7.
(blueprint: lem-trf-section-pullback-coefficient-naturality).
Proof: expand the inverse section compositor followed by the section pullback square.
Naturality of the two inverse-image compositors moves the ambient map a through this
square, after which ha replaces its pullback followed by b. The section-compositor
pasting law leftDerivedUpperStar_map_comp_compSectionIso cancels the two ambient
projection compositors against the two section compositors. Changing the displayed
common composite from w*h to v*z uses equality transport and proof irrelevance. Finally
naturality of the target section compositor moves e to the front. This calculation uses
only functoriality, not a Cartesian square, adjunctions, invertibility of a or e, or
finiteness of A. Identity sections, empty schemes and the zero ring are included. -/
theorem sectionPullback_coefficient_naturality
    (A : Type (u + 1)) [CommRing A]
    {B B' P P' : Scheme.{u}} (v : B' ⟶ B) (p : P ⟶ B) (q : P' ⟶ B')
    (h : P' ⟶ P) (z : B ⟶ P) (w : B' ⟶ P')
    (hp : h ≫ p = q ≫ v) (hz : w ≫ h = v ≫ z)
    (h₀ : z ≫ p = 𝟙 B) (h₁ : w ≫ q = 𝟙 B')
    (K : DerivedCategoryModule A B) (K' : DerivedCategoryModule A B')
    (L : DerivedCategoryModule A P) (L' : DerivedCategoryModule A P')
    (e : (ordinaryFinitePullback A v).obj K ⟶ K')
    (a : (ordinaryFinitePullback A p).obj K ⟶ L)
    (a' : (ordinaryFinitePullback A q).obj K' ⟶ L')
    (b : (ordinaryFinitePullback A h).obj L ⟶ L')
    (ha : (ordinaryFinitePullback A h).map a ≫ b =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h p).inv.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q v (h ≫ p) hp).hom.app K ≫
        (ordinaryFinitePullback A q).map e ≫ a') :
    (ordinaryFinitePullback A v).map
        ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z p h₀).inv.app K ≫
          (ordinaryFinitePullback A z).map a) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v z).inv.app L ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w h (v ≫ z) hz.symm).hom.app L ≫
          (ordinaryFinitePullback A w).map b =
    e ≫ (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) w q h₁).inv.app K' ≫
      (ordinaryFinitePullback A w).map a' := by
  dsimp only [ordinaryFinitePullback] at ha ⊢
  have hn₁ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v z).inv.naturality a
  have hn₂ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    w h (v ≫ z) hz.symm).hom.naturality a
  simp only [Functor.comp_map] at hn₁ hn₂
  simp only [Functor.map_comp, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  erw [reassoc_of% hn₁, reassoc_of% hn₂]
  have hm := ((upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor).map_comp
    (((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor).map a) b
  erw [← hm, ha]
  simp only [Functor.map_comp, Category.assoc]
  have hc := sectionCoefficient_square (ModuleCat.{u + 1} A)
    v p q h z w hp hz h₀ h₁ K
  simp only [Functor.map_comp, Category.assoc] at hc
  erw [reassoc_of% hc]
  have hn := (leftDerivedUpperStarCompSectionIso
    (ModuleCat.{u + 1} A) w q h₁).inv.naturality e
  simp only [Functor.id_map, Functor.comp_map] at hn
  erw [← reassoc_of% hn]

end AlgebraicGeometry.Etale
