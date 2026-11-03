/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
import WeilConjectures.AlgebraicGeometry.ClosedProperModelSiteSquare
import all WeilConjectures.AlgebraicGeometry.ProperEtalePlusComposition
import WeilConjectures.AlgebraicGeometry.OrdinaryBoundaryComposition
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportOriginRestrictionComposition

/-! # Proper normalization of coordinate origin composition -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
private theorem natTrans_eq_of_precompose
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) [F.EssSurj] {G H : D ⥤ E} (α β : G ⟶ H)
    (h : ∀ K, α.app (F.obj K) = β.app (F.obj K)) : α = β := by
  apply NatTrans.ext
  funext Y
  let e := F.objObjPreimageIso Y
  apply (cancel_epi (G.map e.hom)).1
  rw [α.naturality, β.naturality, h]

private theorem derived_comp_inverse
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) :
    Functor.rightDerivedFunctorNatIso e.symm ≪≫ Functor.rightDerivedFunctorCompIso F G =
      (Functor.rightDerivedFunctorCompIso' F G e).symm := by rfl

private theorem inverse_proper_comp
    {D : Type*} [Category* D] {P Q R S T : D}
    (a : P ⟶ Q) (ai : Q ⟶ P) (c : R ⟶ S) (ci : S ⟶ R)
    (e : Q ⟶ S) (w₁ : P ⟶ T) (w₂ : T ⟶ R)
    (ha : ai ≫ a = 𝟙 Q) (hc : c ≫ ci = 𝟙 R)
    (h : a ≫ e = w₁ ≫ w₂ ≫ c) : ai ≫ w₁ ≫ w₂ = e ≫ ci := by
  calc
    ai ≫ w₁ ≫ w₂ = ai ≫ (w₁ ≫ w₂ ≫ c) ≫ ci := by
      simp only [Category.assoc, hc, Category.comp_id]
    _ = ai ≫ (a ≫ e) ≫ ci := by rw [← h]
    _ = e ≫ ci := by simp only [← Category.assoc, ha, Category.id_comp]

private theorem boundary_proper_paste
    {C D : Type*} [Category* C] [Category* D] (N : C ⥤ D)
    {A B E F : C} {P Q : D} (a : A ⟶ B) (ai : B ⟶ A)
    (d : E ⟶ F) (di : F ⟶ E) (e : A ⟶ E) (v : B ⟶ F)
    (b : P ⟶ N.obj B) (r : Q ⟶ N.obj F) (p : P ⟶ Q)
    (ha : ai ≫ a = 𝟙 B) (hd : d ≫ di = 𝟙 E)
    (he : e ≫ d = a ≫ v) (hs : b ≫ N.map v = p ≫ r) :
    (b ≫ N.map ai) ≫ N.map e = p ≫ r ≫ N.map di := by
  have he' : e = a ≫ v ≫ di := by
    calc
      e = (e ≫ d) ≫ di := by simp only [Category.assoc, hd, Category.comp_id]
      _ = (a ≫ v) ≫ di := by rw [he]
      _ = a ≫ v ≫ di := Category.assoc _ _ _
  simp only [he', N.map_comp, Category.assoc]
  rw [← N.map_comp_assoc, ha, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% hs]

private theorem proper_compositor_paste
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (N₀ : C₀ ⥤ D₀) (N₁ : C₁ ⥤ D₁) (N₂ : C₂ ⥤ D₂)
    (F F' : C₀ ⥤ C₁) (G G' : C₁ ⥤ C₂) (H H' : C₀ ⥤ C₂)
    (U U' : D₀ ⥤ D₁) (V V' : D₁ ⥤ D₂) (W W' : D₀ ⥤ D₂)
    (bF : N₀ ⋙ U ≅ F ⋙ N₁) (bG : N₁ ⋙ V ≅ G ⋙ N₂)
    (bH : N₀ ⋙ W ≅ H ⋙ N₂)
    (dF : N₀ ⋙ U' ≅ F' ⋙ N₁) (dG : N₁ ⋙ V' ≅ G' ⋙ N₂)
    (dH : N₀ ⋙ W' ≅ H' ⋙ N₂)
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H')
    (eU : U ≅ U') (eV : V ≅ V') (eW : W ≅ W')
    (α : F ⋙ G ≅ H) (ce : F' ⋙ G' ≅ H') (cp : U' ⋙ V' ≅ W')
    (hF : ∀ K, bF.hom.app K ≫ N₁.map (eF.hom.app K) =
      eU.hom.app (N₀.obj K) ≫ dF.hom.app K)
    (hG : ∀ K, bG.hom.app K ≫ N₂.map (eG.hom.app K) =
      eV.hom.app (N₁.obj K) ≫ dG.hom.app K)
    (hH : ∀ K, bH.hom.app K ≫ N₂.map (eH.hom.app K) =
      eW.hom.app (N₀.obj K) ≫ dH.hom.app K)
    (hα : α.hom ≫ eH.hom =
      Functor.whiskerRight eF.hom G ≫ Functor.whiskerLeft F' eG.hom ≫ ce.hom)
    (hc : ∀ K, V'.map (dF.hom.app K) ≫ dG.hom.app (F'.obj K) ≫
      N₂.map (ce.hom.app K) = cp.hom.app (N₀.obj K) ≫ dH.hom.app K)
    (K : C₀) (ω : V.obj (U.obj (N₀.obj K)) ⟶ W.obj (N₀.obj K))
    (hω : ω = V.map (bF.hom.app K) ≫ bG.hom.app (F.obj K) ≫
      N₂.map (α.hom.app K) ≫ bH.inv.app K) :
    ω ≫ eW.hom.app (N₀.obj K) =
      V.map (eU.hom.app (N₀.obj K)) ≫ eV.hom.app (U'.obj (N₀.obj K)) ≫
        cp.hom.app (N₀.obj K) := by
  rw [hω]
  apply (cancel_mono (dH.hom.app K)).1
  simp only [Category.assoc]
  rw [← hH, Iso.inv_hom_id_app_assoc]
  have hαK := congr_app hα K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hαK
  rw [← N₂.map_comp, hαK, N₂.map_comp, N₂.map_comp]
  have hb := bG.hom.naturality (eF.hom.app K)
  simp only [Functor.comp_map] at hb
  rw [← reassoc_of% hb, ← V.map_comp_assoc, hF, V.map_comp]
  rw [reassoc_of% hG]
  have he := eV.hom.naturality (dF.hom.app K)
  simp only [Category.assoc]
  rw [reassoc_of% he]
  rw [hc]


private theorem restricted_composition_component
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P : ObjectProperty C) (F U : C ⥤ D) (G V : D ⥤ E) (H H' W : C ⥤ E)
    (j : H ⟶ H') (d : P.ι ⋙ H' ⟶ P.ι ⋙ F ⋙ G)
    (a : F ⟶ U) (b : G ⟶ V) (c : H ⟶ W) (e : W ⟶ U ⋙ V)
    (he : (Functor.whiskerLeft P.ι j ≫ d) ≫
        Functor.whiskerRight (Functor.whiskerLeft P.ι a) G ≫
        Functor.whiskerLeft (P.ι ⋙ U) b =
      Functor.whiskerLeft P.ι c ≫ Functor.whiskerLeft P.ι e)
    (K : C) (hK : P K) :
    (j.app K ≫ d.app ⟨K, hK⟩) ≫ G.map (a.app K) ≫ b.app (U.obj K) =
      c.app K ≫ e.app K := by
  exact congr_app he ⟨K, hK⟩

namespace AlgebraicGeometry.ProEtale

set_option linter.auxLemma false in
attribute [local instance 100000] boundedSite._proof_1 boundedSite._proof_2
  boundedSite._proof_5 boundedSite._proof_6 boundedSite._proof_7
  boundedSite._proof_8 boundedSite._proof_9

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftAdjoint Functor.rightAdjoint
  comparisonUpperStar pbcDerivedComparisonRestrict compactSupportSiteComparison
  originCompositionAmbient originCompositionModel
  rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar

private theorem closed_model_square_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [HasCompactification f] :
    (compactSupportSiteComparison A (HasCompactification.compactification f)).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (Functor.whiskerRight
            (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
              (ModuleCat.{u + 1} A) f).hom
            (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) =
      Functor.whiskerLeft (boundedSite A X)
          (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
            (ModuleCat.{u + 1} A) f).hom ≫
        (rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} A) f).hom := by
  rw [closedProperDerivedFactor, Etale.closedProperEtaleDerivedFactor]
  apply NatTrans.ext
  funext K
  exact closedProperModelSiteSquare A f K

private theorem closed_proper_boundary_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [HasCompactification f] :
    (compactBoundary A (HasCompactification.compactification f)).hom ≫
        Functor.whiskerRight (Etale.properLowerShriekPlusIso A f).hom (boundedSite A Y) =
      Functor.whiskerLeft (boundedSite A X)
          (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
            (ModuleCat.{u + 1} A) f).hom ≫ (ordinaryBoundary A f).hom := by
  exact boundary_proper_paste
    ((Functor.whiskeringRight
      (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))).obj
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory)
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).inv
    (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom
    (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.inv
    (Functor.whiskerRight (Etale.properLowerShriekPlusIso A f).hom DerivedCategory.Plus.ι)
    (Functor.whiskerLeft DerivedCategory.Plus.ι
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f).hom)
    (compactSupportSiteComparison A (HasCompactification.compactification f)).hom
    (rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} A) f).hom
    (Functor.whiskerLeft (boundedSite A X)
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) f).hom)
    (Iso.inv_hom_id _) (Iso.hom_inv_id _)
    (Etale.properLowerShriekPlusIso_hom_nat A f) (closed_model_square_nat A f)

private theorem closed_proper_boundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [HasCompactification f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactBoundary A (HasCompactification.compactification f)).hom.app K ≫
      (boundedSite A Y).map ((Etale.properLowerShriekPlusIso A f).hom.app K) =
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} A) f).hom.app ((boundedSite A X).obj K) ≫
      (ordinaryBoundary A f).hom.app K := by
  exact congr_app (closed_proper_boundary_nat A f) K

private theorem ordinary_boundary_comp_inclusion (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
        ((ordinaryBoundary A f).hom.app K) ≫
      (ordinaryBoundary A g).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.obj K) ≫
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory).map
        ((etaleComparisonDirectImageCompIso A f g).hom.app K) =
    (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f)
      (lowerStar (ModuleCat.{u + 1} A) g)
      (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj K)) ≫
      (ordinaryBoundary A (f ≫ g)).hom.app K := by
  exact ordinaryBoundary_comp A f g K

set_option linter.defProp false in
set_option maxHeartbeats 200000 in
-- The specialization retains the cached derived-category instance arguments.
private def closed_model_paste_diagram (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    :=
  letI := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  proper_compositor_paste
    (boundedSite A X) (boundedSite A Y) (boundedSite A Z)
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
      (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g)
      (Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlus
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) (f ≫ g))
      (Etale.lowerStar (ModuleCat.{u + 1} A) (f ≫ g)).rightDerivedFunctorPlus
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
      (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
      (lowerStar (ModuleCat.{u + 1} A) (f ≫ g)).rightDerivedFunctor
    (compactBoundary A (HasCompactification.compactification f))
    (compactBoundary A (HasCompactification.compactification g))
    (compactBoundary A (HasCompactification.compactification (f ≫ g)))
    (ordinaryBoundary A f) (ordinaryBoundary A g) (ordinaryBoundary A (f ≫ g))
    (Etale.properLowerShriekPlusIso A f) (Etale.properLowerShriekPlusIso A g)
    (Etale.properLowerShriekPlusIso A (f ≫ g))
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) f)
        (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) g)
          (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) (f ≫ g))
    (Etale.rightDerivedLowerShriekPlusCompIso A f g)
    (etaleComparisonDirectImageCompIso A f g)
    (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f)
      (lowerStar (ModuleCat.{u + 1} A) g) (lowerStarComp (ModuleCat.{u + 1} A) f g))


set_option linter.defProp false in
set_option maxHeartbeats 200000 in
-- Supply this equation at an explicit object of the fixed diagram.
private def closed_model_paste_f (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    :=
  closed_model_paste_diagram A f g (fun K ↦ closed_proper_boundary A f K)

set_option linter.defProp false in
set_option maxHeartbeats 200000 in
-- Supply this equation at an explicit object of the fixed diagram.
private def closed_model_paste_g (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    :=
  closed_model_paste_f A f g (fun K ↦ closed_proper_boundary A g K)

set_option linter.defProp false in
set_option maxHeartbeats 200000 in
-- Supply this equation at an explicit object of the fixed diagram.
private def closed_model_paste_composite (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    :=
  closed_model_paste_g A f g (fun K ↦ closed_proper_boundary A (f ≫ g) K)

set_option linter.defProp false in
set_option maxHeartbeats 200000 in
-- Supply this equation at an explicit object of the fixed diagram.
private def closed_model_paste_etale (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    :=
  closed_model_paste_composite A f g (Etale.properLowerShriekPlusIso_comp_nat A f g)

set_option linter.defProp false in
set_option maxHeartbeats 200000 in
-- Supply this equation at an explicit object of the fixed diagram.
private def closed_model_paste_data (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    :=
  closed_model_paste_etale A f g (fun K ↦ ordinary_boundary_comp_inclusion A f g K)

set_option maxHeartbeats 200000 in
-- The specialization retains the cached derived-category instance arguments.
private theorem closed_model_word_calculation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (ω : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj ((boundedSite A X).obj L)) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj ((boundedSite A X).obj L))
    (hω : ω =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          ((compactBoundary A (HasCompactification.compactification f)).hom.app L) ≫
        (compactBoundary A (HasCompactification.compactification g)).hom.app
          ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L) ≫
        (boundedSite A Z).map ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L) ≫
        (compactBoundary A (HasCompactification.compactification (f ≫ g))).inv.app L) :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    ω ≫ (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) (f ≫ g)).hom.app ((boundedSite A X).obj L) =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) f).hom.app ((boundedSite A X).obj L)) ≫
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) g).hom.app
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj ((boundedSite A X).obj L)) ≫
      (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f)
        (lowerStar (ModuleCat.{u + 1} A) g)
        (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom.app ((boundedSite A X).obj L) :=
  closed_model_paste_data A f g L ω hω

set_option maxHeartbeats 400000 in
-- Keep the derived-category conversions within this declaration.
private theorem closed_model_comp_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    (originCompositionModel A f g).hom.app L ≫
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) (f ≫ g)).hom.app ((boundedSite A X).obj L) =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) f).hom.app ((boundedSite A X).obj L)) ≫
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) g).hom.app
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj ((boundedSite A X).obj L)) ≫
      (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f)
        (lowerStar (ModuleCat.{u + 1} A) g)
        (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom.app ((boundedSite A X).obj L) := by
  exact closed_model_word_calculation A f g L ((originCompositionModel A f g).hom.app L)
    (origin_model_word A f g L)

set_option maxHeartbeats 400000 in
-- Keep the derived-category conversions within this declaration.
private theorem closed_origin_comp_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    (originCompositionAmbient A f g).hom ≫ Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} A) X).ι) (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) (f ≫ g)).hom =
      Functor.whiskerRight (Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u +
        1} A) X).ι) (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A)
          f).hom)
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) ≫
        Functor.whiskerLeft (((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι) ⋙
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor)
          (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) g).hom ≫
            Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι)
              (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar
                (ModuleCat.{u + 1} A) g) (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom := by
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  apply natTrans_eq_of_precompose (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
  intro L
  change (originCompositionAmbient A f g).hom.app ((comparisonUpperStarPlusEtaleOrigin
    (ModuleCat.{u + 1} A) X).obj L) ≫ _ = _
  rw [origin_model_image]
  exact closed_model_comp_hom A f g L

private theorem closed_origin_comp_inv_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    (originCompositionAmbient A f g).inv ≫
      Functor.whiskerRight (Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u +
        1} A) X).ι) (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A)
          f).hom)
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) ≫
        Functor.whiskerLeft (((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι) ⋙
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor)
          (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) g).hom =
            Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι)
              (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) (f ≫
                g)).hom ≫ Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u +
                  1} A) X).ι)
            (Functor.rightDerivedFunctorNatIso
                (lowerStarComp (ModuleCat.{u + 1} A) f g).symm ≪≫
              Functor.rightDerivedFunctorCompIso (lowerStar (ModuleCat.{u + 1} A) f)
                (lowerStar (ModuleCat.{u + 1} A) g)).hom := by
  have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  dsimp only
  rw [derived_comp_inverse]
  exact inverse_proper_comp (originCompositionAmbient A f g).hom
    (originCompositionAmbient A f g).inv
    (Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι)
      (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar
        (ModuleCat.{u + 1} A) g) (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom)
          (Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι)
            (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar
              (ModuleCat.{u + 1} A) g) (lowerStarComp (ModuleCat.{u + 1} A) f g)).inv)
    (Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι)
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) (f ≫ g)).hom)
    (Functor.whiskerRight (Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u +
      1} A) X).ι)
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) f).hom) (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g))
    (Functor.whiskerLeft (((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι) ⋙
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor)
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) g).hom)
    (Iso.inv_hom_id _) (Iso.hom_inv_id (Functor.isoWhiskerLeft ((DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} A) X).ι) (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u +
        1} A) f) (lowerStar (ModuleCat.{u + 1} A) g) (lowerStarComp (ModuleCat.{u + 1} A) f g))))
    (closed_origin_comp_nat A f g)

set_option maxHeartbeats 400000 in
-- Keep the derived-category conversions within this declaration.
private theorem closed_origin_comp_transport_nat (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (q : h = f ≫ g) [IsClosedImmersion f] [IsClosedImmersion g]
    [IsClosedImmersion h]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification h] :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    (Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι)
      (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A) q).hom ≫
      (originCompositionAmbient A f g).inv) ≫
      Functor.whiskerRight (Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u +
        1} A) X).ι)
        (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) f).hom) (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) ≫
      Functor.whiskerLeft (((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι) ⋙
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor)
        (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) g).hom =
      Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι)
          (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) h).hom ≫
        Functor.whiskerLeft ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι)
          ((Functor.rightDerivedFunctorNatIso
            (lowerStarCongr (ModuleCat.{u + 1} A) q ≪≫
              (lowerStarComp (ModuleCat.{u + 1} A) f g).symm)) ≪≫
          Functor.rightDerivedFunctorCompIso
            (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar (ModuleCat.{u + 1} A) g)).hom := by
  subst h
  dsimp only
  simp only [rightDerivedLowerShriekCongr_rfl, lowerStarCongr_rfl, Iso.refl_trans,
    Iso.refl_hom, Functor.whiskerLeft_id', Category.id_comp]
  exact closed_origin_comp_inv_nat A f g

set_option linter.style.haveILetI false in
set_option maxHeartbeats 400000 in
-- Keep the compositor's injective-preservation witness inlined as in its saved statement.
private theorem closed_origin_comp_inv_plain (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (q : h = f ≫ g) [IsClosedImmersion f] [IsClosedImmersion g]
    [IsClosedImmersion h]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification h]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K) :
    have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
    ((rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A) q).hom.app K ≫
      (originCompositionAmbient A f g).inv.app ⟨K, hK⟩) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) f).hom.app
          K) ≫
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) g).hom.app
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K) =
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) h).hom.app K ≫
      ((Functor.rightDerivedFunctorNatIso (lowerStarCongr (ModuleCat.{u + 1} A) q ≪≫
          (lowerStarComp (ModuleCat.{u + 1} A) f g).symm)) ≪≫
        Functor.rightDerivedFunctorCompIso
          (lowerStar (ModuleCat.{u + 1} A) f)
      (lowerStar (ModuleCat.{u + 1} A) g)).hom.app K := by
  dsimp only
  letI := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  exact restricted_composition_component
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor
    (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A) q).hom
    (originCompositionAmbient A f g).inv
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) f).hom
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) g).hom
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) h).hom
    ((Functor.rightDerivedFunctorNatIso (lowerStarCongr (ModuleCat.{u + 1} A) q ≪≫
      (lowerStarComp (ModuleCat.{u + 1} A) f g).symm)) ≪≫
      Functor.rightDerivedFunctorCompIso
        (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar (ModuleCat.{u + 1} A) g)).hom
    (closed_origin_comp_transport_nat A f g h q) K hK

end AlgebraicGeometry.ProEtale


namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

section

-- Reuse the coordinate definitions' cached instance witnesses when specializing.
set_option linter.auxLemma false in
attribute [local instance 200000] compactProduct._proof_1 compactProduct._proof_2
  compactProduct._proof_3 compactProduct._proof_4 compactProduct._proof_5 compactProduct._proof_6
  sectionTargetIso._proof_1 sectionTargetIso._proof_2
  coordinateComposition._proof_1 coordinateComposition._proof_2
  coordinateComposition._proof_4 coordinateComposition._proof_5

-- Match the generic comparison proof's canonical localization witnesses.
set_option linter.auxLemma false in
attribute [local instance 300000] boundedSite._proof_1 boundedSite._proof_2
  boundedSite._proof_5 boundedSite._proof_6 boundedSite._proof_7
  boundedSite._proof_8 boundedSite._proof_9

attribute [local implicit_reducible] iteratedAffineLine zero
  Scheme.Hom.toIteratedAffineLine AffineSpace.zeroSection

set_option linter.defProp false in
set_option maxHeartbeats 400000 in
-- Infer the specialized object category from the generic comparison itself.
private def coordinate_closed_proper_transport_component
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (r : ℕ)
    (K : D P n B)
    (hK : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (setting P n).Coefficient) B K) :=
  closed_origin_comp_inv_plain (setting P n).Coefficient
    (zero B r) (lastSection B r) (zero B (r + 1))
    (CoordinateTowerNormalization.zero_successor B r).symm K hK

private theorem proof_witness_heq {Q R : Prop} (hQ : Q) (hR : R) : HEq hQ hR := by
  have e : Q = R := propext ⟨fun _ ↦ hR, fun _ ↦ hQ⟩
  cases e
  rfl

meta section

/-- Build congruences through the displayed expression, identifying proof witnesses by
proof irrelevance. Normalize only functor composition and the full-subcategory inclusion,
whose object formulas are definitional. This avoids a large kernel conversion across
implicit endpoints; every generated congruence is subsequently kernel checked. -/
private def structuralProofCongr (fuel : Nat) (a b : Lean.Expr)
    (path : String := "root") : Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => throwError "structural conversion exceeded its expression depth"
  | fuel + 1 =>
    let a := a.consumeMData.headBeta
    let b := b.consumeMData.headBeta
    if a == b then return ← Lean.Meta.mkHEqRefl a
    let expandObject (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
      if e.isAppOf ``Functor.obj then
        let es := e.getAppArgs
        let f := es[es.size - 2]!
        let x := es.back!
        if f.isAppOf ``Functor.comp then
          let fs := f.getAppArgs
          let y ← Lean.Meta.mkAppM ``Functor.obj #[fs[fs.size - 2]!, x]
          return some (← Lean.Meta.mkAppM ``Functor.obj #[fs.back!, y])
        if f.isAppOf ``ObjectProperty.ι &&
            x.isAppOf ``ObjectProperty.FullSubcategory.mk then
          let xs := x.getAppArgs
          return some xs[xs.size - 2]!
      if e.isAppOf ``ObjectProperty.FullSubcategory.obj then
        let x := e.getAppArgs.back!
        if x.isAppOf ``ObjectProperty.FullSubcategory.mk then
          let xs := x.getAppArgs
          return some xs[xs.size - 2]!
      return none
    if let some a' ← expandObject a then
      return ← structuralProofCongr fuel a' b path
    if let some b' ← expandObject b then
      return ← structuralProofCongr fuel a b' path
    if a.isFVar then
      if let some value ← a.fvarId!.getValue? then
        return ← structuralProofCongr fuel value b (path ++ ".zetaL")
    if b.isFVar then
      if let some value ← b.fvarId!.getValue? then
        return ← structuralProofCongr fuel a value (path ++ ".zetaR")
    if a.isLet then
      return ← structuralProofCongr fuel (a.letBody!.instantiate1 a.letValue!) b path
    if b.isLet then
      return ← structuralProofCongr fuel a (b.letBody!.instantiate1 b.letValue!) path
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      return ← Lean.Meta.mkAppM ``proof_witness_heq #[a, b]
    if a.isApp && b.isApp && a.getAppFn == b.getAppFn &&
        a.getAppNumArgs == b.getAppNumArgs then
      let f := a.getAppFn
      let aa := a.getAppArgs
      let bb := b.getAppArgs
      let congr ← Lean.Meta.mkHCongrWithArity f aa.size
      let mut args := #[]
      for i in [:aa.size] do
        let x := aa[i]!
        let y := bb[i]!
        let kind := congr.argKinds[i]!
        let h ← structuralProofCongr fuel x y (path ++ "." ++ toString i)
        match kind with
        | .eq =>
          let h ← Lean.Meta.mkAppM ``eq_of_heq #[h]
          args := args ++ #[x, y, h]
        | .heq => args := args ++ #[x, y, h]
        | _ => throwError "unexpected congruence argument kind"
      let h := Lean.mkAppN congr.proof args
      let ht ← Lean.Meta.whnf (← Lean.Meta.inferType h)
      if ht.isHEq then return h
      else return ← Lean.Meta.mkAppM ``heq_of_eq #[h]
    else
      throwError "structural conversion mismatch at {path}:\n{a}\n{b}"
termination_by fuel

end

end

attribute [local implicit_reducible] iteratedAffineLine zero
  Scheme.Hom.toIteratedAffineLine AffineSpace.zeroSection

set_option cleanup.letToHave true in
/-- Proper comparison carries the coordinate origin compositor to derived composition.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior-product sentence;
originCompositionModel and the counit-defined compactSupportSiteComparison
(blueprint: lem-pur-closed-proper-origin-composition).

Proof: pull the natural-transformation equation back along the etale-origin equivalence.
Its compositor is the word of the three compact-support boundaries and the bounded
etale compositor. Restrict the native compositor using the actual ofRestrict triangle
and common-refinement inclusion squares. The native proper forget-supports equation
then gives the bounded proper compositor equation. The inverse ordinary direct-image
mate composition law gives the ordinary boundary equation. For each closed map, identify
the published proper comparison with its actual clopen-factor model on each site, and
apply the square between the two models. A categorical pasting calculation combines the
three one-map squares with the two compositor equations; cancel the final ordinary
boundary and use naturality to obtain the proper-origin equation. Faithfulness descends
it from the etale-origin equivalence. Invert the compositor, transport along q, and
specialize to the coefficient unit and zero_successor. The calculation retains the
chosen clopen open parts and covers rank zero, empty clopen pieces and zero coefficients. -/
theorem coordinate_closed_proper_origin_composition
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (r : ℕ) :
  let A := (setting P n).Coefficient
  let f := zero B r
  let g := lastSection B r
  let h := zero B (r + 1)
  let q : h = f ≫ g := (CoordinateTowerNormalization.zero_successor B r).symm
  let F := lowerStar (ModuleCat.{u + 1} A) f
  let G := lowerStar (ModuleCat.{u + 1} A) g
  let H := lowerStar (ModuleCat.{u + 1} A) h
  letI : F.PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  let e : H ≅ F ⋙ G := lowerStarCongr (ModuleCat.{u + 1} A) q ≪≫
    (lowerStarComp (ModuleCat.{u + 1} A) f g).symm
  let K := unit P n B
  (coordinateComposition P n B r).hom ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) f).hom.app K) ≫
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) g).hom.app (F.rightDerivedFunctor.obj K) =
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} A) h).hom.app K ≫
      ((Functor.rightDerivedFunctorNatIso e) ≪≫
        Functor.rightDerivedFunctorCompIso F G).hom.app K := by
  intro A f g h q F G H e K
  conv_lhs =>
    lhs
    unfold coordinateComposition
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  have h₀ := coordinate_closed_proper_transport_component P n B r K (unit_origin P n B)
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `h₀
        | throwError "missing coordinate comparison hypothesis"
      let h := hd.toExpr
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← Lean.instantiateMVars (← goal.getType)
      let source ← Lean.instantiateMVars (← Lean.Meta.inferType h)
      let he ← structuralProofCongr 200 target source
      let e ← Lean.Meta.mkAppM ``eq_of_heq #[he]
      goal.assign (← Lean.Meta.mkAppM ``Eq.mpr #[e, h])
      Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale.AffineZeroPurity
