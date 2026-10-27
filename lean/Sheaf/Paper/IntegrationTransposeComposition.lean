/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegrationTransposeCompositionData
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Sheaf.Paper.IntegrationUnitNormalization
import Sheaf.Paper.IteratedIntegration
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # Composition of actual adjoint transposes of integration

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-integration-transpose-composition).
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale.IntegrationComposition

variable {A : Type (u + 1)} [CommRing A] {X Y Z : Scheme.{u}}

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

private instance symmetry_component_isIso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (S : Scheme.{u}) (K L : _root_.DerivedCategory (Sheaf S.smallEtaleTopology B)) :
    IsIso (((derivedTensorSymmetry B S).hom.app K).app L) :=
  (((derivedTensorSymmetry B S).app K).app L).isIso_hom

private instance symmetry_inv_component_isIso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (S : Scheme.{u}) (K L : _root_.DerivedCategory (Sheaf S.smallEtaleTopology B)) :
    IsIso (((derivedTensorSymmetry B S).inv.app K).app L) :=
  (((derivedTensorSymmetry B S).app K).app L).isIso_inv

private theorem conjugate_projection_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    (s : T ≅ T.flip) (t : U ≅ U.flip)
    (F : C ⥤ D) (L P : D ⥤ C) (e : L ≅ P)
    (p : ∀ W K, (U.obj (F.obj W)).obj K ⟶ F.obj ((T.obj W).obj (L.obj K)))
    (hnw : ∀ {W W'} (w : W ⟶ W') K,
      (U.map (F.map w)).app K ≫ p W' K = p W K ≫ F.map ((T.map w).app _))
    (hnk : ∀ W {K K'} (k : K ⟶ K'),
      (U.obj (F.obj W)).map k ≫ p W K' = p W K ≫ F.map ((T.obj W).map (L.map k)))
    {W W' : C} {K K' : D} (w : W ⟶ W') (k : K ⟶ K') :
    (U.map k).app _ ≫ (U.obj K').map (F.map w) ≫
        (t.hom.app K').app _ ≫ p W' K' ≫
        F.map ((T.obj W').map (e.hom.app K')) ≫ F.map ((s.inv.app _).app W') =
      (t.hom.app K).app _ ≫ p W K ≫
        F.map ((T.obj W).map (e.hom.app K)) ≫ F.map ((s.inv.app _).app W) ≫
        F.map ((T.map (P.map k)).app W ≫ (T.obj _).map w) := by
  have ht₁ := (t.hom.app K').naturality (F.map w)
  have ht₂ := congr_app (t.hom.naturality k) (F.obj W)
  have hs₁ := (s.inv.app (P.obj K')).naturality w
  have hs₂ := congr_app (s.inv.naturality (P.map k)) W
  simp only [NatTrans.comp_app, Functor.flip_obj_obj, Functor.flip_obj_map,
    Functor.flip_map_app] at ht₁ ht₂ hs₁ hs₂
  simp only [Functor.map_comp]
  rw [reassoc_of% ht₁, reassoc_of% ht₂, reassoc_of% hnw w K', reassoc_of% hnk W k]
  have hw := (T.map w).naturality (e.hom.app K')
  have hk := congrArg ((T.obj W).map) (e.hom.naturality k)
  simp only [Functor.map_comp] at hk
  have hinner : (T.obj W).map (L.map k) ≫ (T.map w).app (L.obj K') ≫
      (T.obj W').map (e.hom.app K') ≫ (s.inv.app (P.obj K')).app W' =
      (T.obj W).map (e.hom.app K) ≫ (s.inv.app (P.obj K)).app W ≫
        (T.map (P.map k)).app W ≫ (T.obj (P.obj K')).map w := by
    rw [← reassoc_of% hw, reassoc_of% hk, hs₁, reassoc_of% hs₂]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ (t.hom.app K).app (F.obj W) ≫ p W K ≫ F.map z) hinner

private theorem projection_naturality (f : X ⟶ Y) [HasCompactification f]
    {W W' : DerivedCategoryModule A X} {K K' : DerivedCategoryModule A Y}
    (w : W ⟶ W') (k : K ⟶ K') :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map k).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K').map
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map w) ≫
        compactSupportProjectionMap A f W' K' =
      compactSupportProjectionMap A f W K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).map
            ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map k)).app W ≫
              ((derivedTensor (ModuleCat.{u + 1} A) X).obj _).map w) := by
  have h := conjugate_projection_naturality
    (derivedTensor (ModuleCat.{u + 1} A) X) (derivedTensor (ModuleCat.{u + 1} A) Y)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) X)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) Y)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) _ _
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (fun W K ↦ ((projectionMap (ModuleCat.{u + 1} A) f).app W).app K)
    (fun w K ↦ congr_app ((projectionMap (ModuleCat.{u + 1} A) f).naturality w) K)
    (fun W {_ _} k ↦ ((projectionMap (ModuleCat.{u + 1} A) f).app W).naturality k) w k
  simpa only [compactSupportProjectionMap, compactSupportProjectionMapOfCompactification,
    projectionMap, rightDerivedLowerShriek, Category.assoc] using h

private theorem projection_left_of_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D) (P : D ⥤ C)
    (q : ∀ W K, (U.obj K).obj (F.obj W) ⟶ F.obj ((T.obj (P.obj K)).obj W))
    (hn : ∀ {W W'} {K K'} (w : W ⟶ W') (k : K ⟶ K'),
      (U.map k).app _ ≫ (U.obj K').map (F.map w) ≫ q W' K' =
        q W K ≫ F.map ((T.map (P.map k)).app W ≫ (T.obj _).map w))
    {W W'} (w : W ⟶ W') (K : D) :
    (U.obj K).map (F.map w) ≫ q W' K = q W K ≫ F.map ((T.obj _).map w) := by
  have h := hn w (𝟙 K)
  rw [U.map_id, NatTrans.id_app, P.map_id, T.map_id, NatTrans.id_app] at h
  simpa only [Category.id_comp] using h

private theorem projection_right_of_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D) (P : D ⥤ C)
    (q : ∀ W K, (U.obj K).obj (F.obj W) ⟶ F.obj ((T.obj (P.obj K)).obj W))
    (hn : ∀ {W W'} {K K'} (w : W ⟶ W') (k : K ⟶ K'),
      (U.map k).app _ ≫ (U.obj K').map (F.map w) ≫ q W' K' =
        q W K ≫ F.map ((T.map (P.map k)).app W ≫ (T.obj _).map w))
    (W : C) {K K'} (k : K ⟶ K') :
    (U.map k).app _ ≫ q W K' = q W K ≫ F.map ((T.map (P.map k)).app W) := by
  have h := hn (𝟙 W) k
  rw [F.map_id, (U.obj K').map_id, (T.obj (P.obj K')).map_id] at h
  simpa only [Category.id_comp, Category.comp_id] using h

private theorem projection_left (f : X ⟶ Y) [HasCompactification f]
    {W W' : DerivedCategoryModule A X} (w : W ⟶ W') (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map w) ≫
        compactSupportProjectionMap A f W' K = compactSupportProjectionMap A f W K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).map w) :=
  projection_left_of_naturality _ _ _ _ (compactSupportProjectionMap A f)
    (fun w k ↦ projection_naturality f w k) w K

private theorem projection_right (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X) {K K' : DerivedCategoryModule A Y} (k : K ⟶ K') :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map k).app _ ≫
        compactSupportProjectionMap A f W K' = compactSupportProjectionMap A f W K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map k)).app W) :=
  projection_right_of_naturality _ _ _ _ (compactSupportProjectionMap A f)
    (fun w k ↦ projection_naturality f w k) W k

private theorem tensor_unit_trace
    {C : Type*} [Category C] [MonoidalCategory C]
    {M : C} (t : M ⟶ 𝟙_ C) :
    (λ_ M).inv ≫ (𝟙_ C ◁ t) ≫ (ρ_ (𝟙_ C)).hom = t := by
  rw [← reassoc_of% leftUnitor_inv_naturality t]
  monoidal

private theorem generic_tensor_unit_trace
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (S : Scheme.{u}) {M : _root_.DerivedCategory (Sheaf S.smallEtaleTopology B)}
    (t : M ⟶ 𝟙_ _) :
    (derivedTensorLeftUnitor B S M).inv ≫ ((derivedTensor B S).obj (𝟙_ _)).map t ≫
      (derivedTensorRightUnitor B S (𝟙_ _)).hom = t :=
  tensor_unit_trace t

private theorem inverse_square
    {C : Type*} [Category C] {V Q W : C} (u : Q ≅ W) (v : V ≅ W)
    (p : V ⟶ Q) [IsIso p] (hp : p ≫ u.hom = v.hom) :
    u.inv ≫ inv p = v.inv := by
  apply (cancel_mono v.hom).1
  rw [← hp]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, u.inv_hom_id]
  rw [hp, v.inv_hom_id]

private theorem unit_contraction
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (R : D ⥤ C) (adj : F ⊣ R)
    (W Q : C) (I V : D) (e : Q ≅ W) (l : V ≅ F.obj W)
    (p : V ⟶ F.obj Q) [IsIso p] (h : p ≫ F.map e.hom = l.hom)
    (t : F.obj W ⟶ I) (j : V ⟶ I) (hj : l.inv ≫ j = t) :
    e.inv ≫ adj.homEquiv _ _ (inv p ≫ j) = adj.homEquiv _ _ t := by
  rw [← adj.homEquiv_naturality_left]
  congr 1
  have hi := inverse_square (F.mapIso e) l p h
  simp only [Functor.mapIso_inv] at hi
  rw [← Category.assoc, hi, hj]

private theorem orientation_trace (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K)) :
    orientation f R adj W t hP = adj.homEquiv _ _ t := by
  have := hP (𝟙_ _)
  have hj := generic_tensor_unit_trace (ModuleCat.{u + 1} A) Y t
  exact unit_contraction (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) R adj W _
    (𝟙_ _) _ (unitObjectIso f W)
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W))
    (compactSupportProjectionMap A f W (𝟙_ _)) (integration_unit_normalization f W) t
    (((derivedTensor (ModuleCat.{u + 1} A) Y).obj (𝟙_ _)).map t ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y (𝟙_ _)).hom) hj

private theorem inverse_naturality
    {C : Type*} [Category C] {W X Y Z : C}
    (p : W ⟶ X) (q : Y ⟶ Z) [IsIso p] [IsIso q]
    (a : W ⟶ Y) (b : X ⟶ Z) (h : a ≫ q = p ≫ b) :
    b ≫ inv q = inv p ≫ a := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact h.symm

private theorem adjoint_composition
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    {Rf : D ⥤ C} {Rg : E ⥤ D} {Rh : E ⥤ C}
    (af : F ⊣ Rf) (ag : G ⊣ Rg) (ah : H ⊣ Rh) (α : F ⋙ G ≅ H)
    {S T : C} {U : D} {K : E} (a : S ⟶ T) (b : T ⟶ Rf.obj U)
    (v : U ⟶ Rg.obj K) (h : H.obj S ⟶ K)
    (he : α.hom.app S ≫ h =
      G.map (F.map a ≫ (af.homEquiv _ _).symm b) ≫ (ag.homEquiv _ _).symm v) :
    ah.homEquiv _ _ h = a ≫ b ≫ Rf.map v ≫
      (ah.rightAdjointUniq ((af.comp ag).ofNatIsoLeft α)).inv.app K := by
  let ac := (af.comp ag).ofNatIsoLeft α
  have hm : ah.homEquiv _ _ h ≫ (ah.rightAdjointUniq ac).hom.app K =
      ac.homEquiv _ _ h := by
    simp only [Adjunction.homEquiv_unit, Category.assoc]
    rw [(ah.rightAdjointUniq ac).hom.naturality h,
      Adjunction.unit_rightAdjointUniq_hom_app_assoc]
  apply (cancel_mono ((ah.rightAdjointUniq ac).hom.app K)).1
  change _ = (a ≫ b ≫ Rf.map v ≫ (ah.rightAdjointUniq ac).inv.app K) ≫ _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hm, Adjunction.homEquiv_ofNatIsoLeft_apply, he, Adjunction.comp_homEquiv]
  change af.homEquiv _ _ (ag.homEquiv _ _ _) = _
  rw [ag.homEquiv_naturality_left, Equiv.apply_symm_apply,
    af.homEquiv_naturality_right, af.homEquiv_naturality_left,
    Equiv.apply_symm_apply]
  simp only [Category.assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]


private theorem tensor_adjunct_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (P : D ⥤ C)
    (F : C ⥤ D) (R : D ⥤ C) (adj : F ⊣ R) (I L : D)
    (W : C) (v : W ⟶ R.obj I) (t : F.obj W ⟶ I)
    (r : (U.obj L).obj I ⟶ L)
    (p : (U.obj L).obj (F.obj W) ⟶ F.obj ((T.obj (P.obj L)).obj W))
    (q : (U.obj L).obj (F.obj (R.obj I)) ⟶ F.obj ((T.obj (P.obj L)).obj (R.obj I)))
    [IsIso p] [IsIso q]
    (hn : (U.obj L).map (F.map v) ≫ q = p ≫ F.map ((T.obj (P.obj L)).map v))
    (hv : F.map v ≫ adj.counit.app I = t) :
    (T.obj (P.obj L)).map v ≫
      adj.homEquiv _ _ (inv q ≫ (U.obj L).map (adj.counit.app I) ≫ r) =
      adj.homEquiv _ _ (inv p ≫ (U.obj L).map t ≫ r) := by
  rw [← adj.homEquiv_naturality_left]
  apply congrArg (adj.homEquiv _ _)
  rw [reassoc_of% inverse_naturality p q _ _ hn,
    ← (U.obj L).map_comp_assoc, hv]

private theorem tensor_integration_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (P : D ⥤ C) (F : C ⥤ D)
    (I : D) (r : ∀ K, (U.obj K).obj I ⟶ K)
    (hr : ∀ {K K'} (k : K ⟶ K'), (U.map k).app I ≫ r K' = r K ≫ k)
    (W : C) (t : F.obj W ⟶ I) {K K' : D} (k : K ⟶ K')
    (p : (U.obj K).obj (F.obj W) ⟶ F.obj ((T.obj (P.obj K)).obj W))
    (q : (U.obj K').obj (F.obj W) ⟶ F.obj ((T.obj (P.obj K')).obj W))
    [IsIso p] [IsIso q]
    (hn : (U.map k).app (F.obj W) ≫ q =
      p ≫ F.map ((T.map (P.map k)).app W)) :
    F.map ((T.map (P.map k)).app W) ≫ inv q ≫ (U.obj K').map t ≫ r K' =
      (inv p ≫ (U.obj K).map t ≫ r K) ≫ k := by
  rw [reassoc_of% inverse_naturality p q _ _ hn]
  rw [← reassoc_of% (U.map k).naturality t]
  simp only [Category.assoc]
  rw [hr k]

private theorem generic_right_unitor_naturality
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (S : Scheme.{u}) {K K' : _root_.DerivedCategory (Sheaf S.smallEtaleTopology B)}
    (k : K ⟶ K') :
    ((derivedTensor B S).map k).app (𝟙_ _) ≫ (derivedTensorRightUnitor B S K').hom =
      (derivedTensorRightUnitor B S K).hom ≫ k :=
  rightUnitor_naturality k

private theorem integration_naturality (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K))
    {K K' : DerivedCategoryModule A Y} (k : K ⟶ K') :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map k)).app W) ≫
        integration f W t hP K' = integration f W t hP K ≫ k := by
  have := hP K
  have := hP K'
  exact tensor_integration_naturality
    (derivedTensor (ModuleCat.{u + 1} A) X) (derivedTensor (ModuleCat.{u + 1} A) Y)
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) (𝟙_ _)
    (fun K ↦ (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom)
    (fun k ↦ generic_right_unitor_naturality (ModuleCat.{u + 1} A) Y k)
    W t k (compactSupportProjectionMap A f W K) (compactSupportProjectionMap A f W K')
    (projection_right f W k)

private theorem gamma_naturality (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K))
    {K K' : DerivedCategoryModule A Y} (k : K ⟶ K') :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map k)).app W ≫
        gamma f R adj W t hP K' = gamma f R adj W t hP K ≫ R.map k :=
  adj.homEquiv_naturality_left_square _ _ _ _ (integration_naturality f W t hP k)

private theorem gamma_orientation (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K))
    (L : DerivedCategoryModule A Y)
    (hQ : IsIso (compactSupportProjectionMap A f (R.obj (𝟙_ _)) L)) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj L)).map
      (orientation f R adj W t hP) ≫ theta f R adj L hQ = gamma f R adj W t hP L := by
  have := hP L
  have := hQ
  let v := orientation f R adj W t hP
  have hv : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map v ≫
      adj.counit.app (𝟙_ _) = t := by
    rw [show v = adj.homEquiv _ _ t from orientation_trace f R adj W t hP]
    exact (adj.homEquiv _ _).symm_apply_apply t
  have hn := projection_left f v L
  simpa only [theta, gamma, integration, object] using tensor_adjunct_naturality
    (derivedTensor (ModuleCat.{u + 1} A) X) (derivedTensor (ModuleCat.{u + 1} A) Y)
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) R adj (𝟙_ _) L W v t
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y L).hom
    (compactSupportProjectionMap A f W L) (compactSupportProjectionMap A f (R.obj (𝟙_ _)) L)
    hn hv

/-- Composition of integration transposes, the orientation/dualizing tensor identity,
transfer of projection invertibility along the orientation, and the even-block sign.
Source: cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-integration-transpose-composition).

Proof (the eight steps of the node):
1. Fix the normalized derived associators and exact pullback tensor/composition comparisons.
   On total-complex summands the open comparison sends b tensor (b' tensor m) to their
   restrictions tensor m. Its two-coefficient and unit laws descend from resolving tuples.
2. Combine proper projection tensor coherence with the open law. Naturality moves the
   open comparison through the proper projection. Inverting gives the two-coefficient
   law for inverse projection Q. Its unit map is the identity by adjunct-counit identity.
3. The inverse transpose of gamma is integration. At the unit this gives
   epsilon F(orientation) = t. Naturality of Q in W then identifies the inverse transpose
   of theta (1 tensor orientation) with integration; injectivity proves the second clause.
4. Under adjf.comp adjg, untranspose the proposed composite of gammas. Naturality of Qf
   along gamma_g moves the latter through Qf, also at the ambient input Rg(K).
5. Apply the two-coefficient law with g* K and Wg and then naturality of Qg along
   beta = integration_f(Wg). The transpose becomes the iterated inverse projection
   followed by 1 tensor (tg Fg(beta)).
6. The inverse composition law of lem-amb-shriek-tensor-composition rewrites that map as
   integration_h followed on its domain by alpha. Insert the trace hypothesis. The right
   mate has the same transpose, so injectivity and its inverse prove the first clause.
7. Naturality of projection in orientation, which is invertible in this clause, gives a
   square with three invertible sides. The remaining projection is invertible for every
   L, including Rg(K). This applies in particular to the vector-bundle twist/shift objects.
8. The normalized total tensor symmetry gives block coefficient (-1)^(ab). At a=2r and
   b=2s this is 1. Ordered reassociation itself interchanges no blocks.
-/
theorem integrationTransposeComposition
    [Finite A] [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (Rf : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (Rg : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A Y)
    (Rh : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A X)
    (adjf : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ Rf)
    (adjg : rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⊣ Rg)
    (adjh : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) ⊣ Rh)
    (Wf : DerivedCategoryModule A X) (Wg : DerivedCategoryModule A Y)
    (tf : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj Wf ⟶ 𝟙_ _)
    (tg : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj Wg ⟶ 𝟙_ _)
    (th : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj
      (object f Wf Wg) ⟶ 𝟙_ _)
    (hPf : ∀ L : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f Wf L))
    (hPg : ∀ K : DerivedCategoryModule A Z, IsIso (compactSupportProjectionMap A g Wg K))
    (hPh : ∀ K : DerivedCategoryModule A Z,
      IsIso (compactSupportProjectionMap A (f ≫ g) (object f Wf Wg) K))
    (ht : (unboundedEtaleLowerShriekCompIso A f g).hom.app (object f Wf Wg) ≫ th =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map (integration f Wf tf hPf Wg) ≫ tg)
    (K : DerivedCategoryModule A Z) :
    (gamma (f ≫ g) Rh adjh (object f Wf Wg) th hPh K =
      (reassociation f g Wf Wg K).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
            (gamma g Rg adjg Wg tg hPg K))).app Wf ≫
        gamma f Rf adjf Wf tf hPf (Rg.obj K) ≫
        (rightMate f g Rf Rg Rh adjf adjg adjh).inv.app K) ∧
    (∀ (L : DerivedCategoryModule A Y)
        (hPomega : IsIso (compactSupportProjectionMap A f (Rf.obj (𝟙_ _)) L)),
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj L)).map
        (orientation f Rf adjf Wf tf hPf) ≫ theta f Rf adjf L hPomega =
        gamma f Rf adjf Wf tf hPf L) ∧
    (∀ (N r s : ℕ) (hA : (N : A) = 0),
      Wf = ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist X N A hA r))⟦2 * (r : ℤ)⟧ →
      Wg = ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist Y N A hA s))⟦2 * (s : ℤ)⟧ →
      IsIso (orientation f Rf adjf Wf tf hPf) →
      ∀ L : DerivedCategoryModule A Y,
        IsIso (compactSupportProjectionMap A f (Rf.obj (𝟙_ _)) L)) ∧
    (∀ r s : ℕ, (-1 : ℤ) ^ ((2 * r) * (2 * s)) = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc := adjoint_composition adjf adjg adjh
      (unboundedEtaleLowerShriekCompIso A f g) (reassociation f g Wf Wg K).hom
      (gamma f Rf adjf Wf tf hPf (object g Wg K))
      (gamma g Rg adjg Wg tg hPg K)
      (integration (f ≫ g) (object f Wf Wg) th hPh K)
      (by simpa only [gamma, Equiv.symm_apply_apply] using
        iterated_integration f g Wf Wg tf tg th hPf hPg hPh ht K)
    have hn := gamma_naturality f Rf adjf Wf tf hPf (gamma g Rg adjg Wg tg hPg K)
    change gamma (f ≫ g) Rh adjh (object f Wf Wg) th hPh K = _ at hc
    rw [← reassoc_of% hn] at hc
    unfold rightMate
    with_reducible exact hc
  · intro L hPomega
    exact gamma_orientation f Rf adjf Wf tf hPf L hPomega
  · intro N r s hA hWf hWg hv L
    have := isIso_projectionMap_of_finite A f
    have hp : IsIso (((projectionMap (ModuleCat.{u + 1} A) f).app
        (Rf.obj (𝟙_ _))).app L) := inferInstance
    change IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f)).app (Rf.obj (𝟙_ _))).app L) at hp
    unfold compactSupportProjectionMap compactSupportProjectionMapOfCompactification
    infer_instance
  · intro r s
    simp [Nat.mul_assoc, pow_mul]

end AlgebraicGeometry.Etale.IntegrationComposition
