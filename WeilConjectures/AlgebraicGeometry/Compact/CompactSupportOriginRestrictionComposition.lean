/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Restriction.EtaleRestrictionCompositor
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.AlgebraicGeometry.Proper.ProperRestrictionSiteSquare
import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionSiteSquare
import all WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition

/-! # Scalar restriction and the compositor on etale-origin complexes

Source: Stacks Project, Tags 09AF, 099R, 0F7J and 0GL6
(blueprint: lem-sf-origin-compact-restriction-composition).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem boundary_cube_paste
    {EA₀ EA₁ EA₂ EB₀ EB₁ EB₂ PA₀ PA₁ PA₂ PB₀ PB₁ PB₂ : Type*}
    [Category EA₀] [Category EA₁] [Category EA₂]
    [Category EB₀] [Category EB₁] [Category EB₂]
    [Category PA₀] [Category PA₁] [Category PA₂]
    [Category PB₀] [Category PB₁] [Category PB₂]
    (VA₀ : EA₀ ⥤ PA₀) (VA₁ : EA₁ ⥤ PA₁) (VA₂ : EA₂ ⥤ PA₂)
    (VB₀ : EB₀ ⥤ PB₀) (VB₁ : EB₁ ⥤ PB₁) (VB₂ : EB₂ ⥤ PB₂)
    (RE₀ : EB₀ ⥤ EA₀) (RE₁ : EB₁ ⥤ EA₁) (RE₂ : EB₂ ⥤ EA₂)
    (RP₀ : PB₀ ⥤ PA₀) (RP₁ : PB₁ ⥤ PA₁) (RP₂ : PB₂ ⥤ PA₂)
    (FA : EA₀ ⥤ EA₁) (GA : EA₁ ⥤ EA₂)
    (FB : EB₀ ⥤ EB₁) (GB : EB₁ ⥤ EB₂)
    (FP : PA₀ ⥤ PA₁) (GP : PA₁ ⥤ PA₂)
    (FQ : PB₀ ⥤ PB₁) (GQ : PB₁ ⥤ PB₂)
    (d₀ : RE₀ ⋙ VA₀ ≅ VB₀ ⋙ RP₀)
    (d₁ : RE₁ ⋙ VA₁ ≅ VB₁ ⋙ RP₁)
    (d₂ : RE₂ ⋙ VA₂ ≅ VB₂ ⋙ RP₂)
    (bFA : VA₀ ⋙ FP ≅ FA ⋙ VA₁) (bGA : VA₁ ⋙ GP ≅ GA ⋙ VA₂)
    (bFB : VB₀ ⋙ FQ ≅ FB ⋙ VB₁) (bGB : VB₁ ⋙ GQ ≅ GB ⋙ VB₂)
    (cFE : RE₀ ⋙ FA ⟶ FB ⋙ RE₁) (cGE : RE₁ ⋙ GA ⟶ GB ⋙ RE₂)
    (cFP : RP₀ ⋙ FP ⟶ FQ ⋙ RP₁) (cGP : RP₁ ⋙ GP ⟶ GQ ⋙ RP₂)
    (hF : ∀ L, FP.map (d₀.hom.app L) ≫ cFP.app (VB₀.obj L) ≫
      RP₁.map (bFB.hom.app L) = bFA.hom.app (RE₀.obj L) ≫
        VA₁.map (cFE.app L) ≫ d₁.hom.app (FB.obj L))
    (hG : ∀ L, GP.map (d₁.hom.app L) ≫ cGP.app (VB₁.obj L) ≫
      RP₂.map (bGB.hom.app L) = bGA.hom.app (RE₁.obj L) ≫
        VA₂.map (cGE.app L) ≫ d₂.hom.app (GB.obj L))
    (L : EB₀) :
    GP.map (FP.map (d₀.hom.app L)) ≫ GP.map (cFP.app (VB₀.obj L)) ≫
      cGP.app (FQ.obj (VB₀.obj L)) ≫
      RP₂.map (GQ.map (bFB.hom.app L) ≫ bGB.hom.app (FB.obj L)) =
    GP.map (bFA.hom.app (RE₀.obj L)) ≫ bGA.hom.app (FA.obj (RE₀.obj L)) ≫
      VA₂.map (GA.map (cFE.app L) ≫ cGE.app (FB.obj L)) ≫
      d₂.hom.app (GB.obj (FB.obj L)) := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := cGP.naturality (bFB.hom.app L)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← GP.map_comp_assoc, ← GP.map_comp_assoc]
  simp only [Category.assoc]
  rw [hF]
  simp only [Functor.map_comp, Category.assoc]
  rw [hG]
  have hb := bGA.hom.naturality (cFE.app L)
  dsimp only [Functor.comp_map] at hb
  rw [reassoc_of% hb]

private theorem pasted_boundary_word
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₀ X₁ X₂ : C} {Y₀ Y₁ Y₂ Y₃ Y₄ : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : F.obj X₂ ⟶ Y₀)
    (d : Y₀ ⟶ Y₁) (e : Y₁ ⟶ Y₂) (f : Y₂ ⟶ Y₃) (g : Y₃ ⟶ Y₄) :
    F.map a ≫ F.map b ≫ c ≫ d ≫ e ≫ f ≫ g =
      F.map (a ≫ b) ≫ (c ≫ d) ≫ e ≫ (f ≫ g) := by
  simp only [Functor.map_comp, Category.assoc]

private theorem transport_square
    {C : Type*} [Category C] {S₀ S T₀ T V₀ V : C}
    (u : S₀ ⟶ S) [Epi u] (l₀ : S₀ ⟶ T₀) (l : S ⟶ T)
    (a₀ : S₀ ⟶ V₀) (a : S ⟶ V) (v : V₀ ⟶ V)
    (c₀ : V₀ ⟶ T₀) (c : V ⟶ T) (w : T₀ ⟶ T)
    (hl : u ≫ l = l₀ ≫ w) (h₀ : l₀ = a₀ ≫ c₀)
    (hc : v ≫ c = c₀ ≫ w) (ha : u ≫ a = a₀ ≫ v) : l = a ≫ c := by
  apply (cancel_epi u).mp
  rw [hl, h₀, Category.assoc, ← hc, ← reassoc_of% ha]

private theorem transport_compositor
    {C : Type*} [Category C] {T₀ T₁ T₂ T₃ T₄ : C}
    (u : T₀ ⟶ T₁) [Epi u] (l : T₁ ⟶ T₄) (a : T₁ ⟶ T₃)
    (x : T₀ ⟶ T₂) (v : T₂ ⟶ T₃) (r : T₃ ⟶ T₄)
    (h : u ≫ l = x ≫ v ≫ r) (hn : u ≫ a = x ≫ v) : l = a ≫ r := by
  apply (cancel_epi u).mp
  rw [reassoc_of% hn]
  exact h

private theorem restriction_origin
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u})
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X L) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L) := by
  rcases hL with ⟨K, hK, ⟨e⟩⟩
  let K' := (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj ⟨K, hK⟩
  refine ⟨K'.obj, K'.property, ⟨?_⟩⟩
  exact ((pbcDerivedComparisonRestrict X φ).app K).symm ≪≫
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).mapIso e

private noncomputable def boundedSite (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :=
  DerivedCategory.Plus.ι ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

private noncomputable def scalarSitePlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙ boundedSite A T ≅
      boundedSite B T ⋙ Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ :=
  NatIso.ofComponents (fun L ↦ ((pbcDerivedComparisonRestrict T φ).app L.obj).symm)
    (fun t ↦ (pbcDerivedComparisonRestrict T φ).inv.naturality t.hom)

private noncomputable def compactBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    boundedSite A X ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ⋙
        boundedSite A Y :=
  compactSupportSiteComparison A c ≪≫ Functor.isoWhiskerRight
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).symm
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory

private theorem compactBoundary_paste (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    compactBoundary A c =
  Functor.isoWhiskerRight (openRestrictionSiteBoundary A c.i)
      (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor ≪≫
    Functor.isoWhiskerLeft
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus
      (properRestrictionSiteBoundary A c.g) := by
  dsimp only [compactBoundary]
  symm
  rw [← compactSupportComparisonNormalization]
  ext L
  simp only [openRestrictionSiteBoundary, properRestrictionSiteBoundary,
    fixedCompactSupportComparisonIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.map_comp, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc]
  repeat' first
    | erw [((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map_id]
    | erw [Category.id_comp]

private theorem compactBoundary_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((scalarSitePlus φ X).hom.app L) ≫
      (compactSupportRestrictionIso φ c).hom.app ((boundedSite B X).obj L) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((compactBoundary B c).hom.app L) =
    (compactBoundary A c).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (boundedSite A Y).map ((Etale.compactSupportCoefficientRestrictionPlus φ c).hom.app L) ≫
      (scalarSitePlus φ Y).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c).obj L) := by
  simp only [compactBoundary_paste]
  have h := boundary_cube_paste
    (boundedSite A X) (boundedSite A c.Z) (boundedSite A Y)
    (boundedSite B X) (boundedSite B c.Z) (boundedSite B Y)
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus
    (Sheaf.restrictScalars c.Z.smallEtaleTopology φ).mapDerivedCategoryPlus
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology c.Z) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus
    (Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorPlus
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategoryPlus
    (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctorPlus
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
    (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
    (scalarSitePlus φ X) (scalarSitePlus φ c.Z) (scalarSitePlus φ Y)
    (openRestrictionSiteBoundary A c.i) (properRestrictionSiteBoundary A c.g)
    (openRestrictionSiteBoundary B c.i) (properRestrictionSiteBoundary B c.g)
    (Etale.coefficientRestrictionOpenPlus φ c.i).hom
    (asIso (Etale.rightDerivedLowerStarRestrictScalars φ c.g)).inv
    (fixedScalarRestrictionOpen φ c.i).hom
    (fixedScalarRestrictionDirectImage φ c.g).hom
    (openRestriction_site_square φ c.i) (properRestriction_site_square φ c.g) L
  simpa only [compactSupportRestrictionIso,
    Etale.compactSupportCoefficientRestrictionPlus, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.comp_map, Functor.comp_obj] using h

private noncomputable def restrictionOrigin
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u}) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).FullSubcategory ⥤
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory :=
  ObjectProperty.lift _
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).ι ⋙
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
    (fun L ↦ restriction_origin φ X L.obj L.property)

-- Keep the sheaf and resolution constructions abstract in the transport calculation.
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftAdjoint Functor.rightAdjoint
  comparisonUpperStar pbcDerivedComparisonRestrict compactSupportSiteComparison

attribute [local irreducible] originCompositionAmbient originCompositionModel

private theorem origin_model_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (originCompositionAmbient A f g).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
    (originCompositionModel A f g).hom.app L := by
  let I := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  have hm := (H.whiskeringRight _).map_preimage
    (X := originCompactSupport A f ⋙ originCompactSupport A g)
    (Y := originCompactSupport A (f ≫ g))
    (originCompositionAmbient A f g).hom
  change Functor.whiskerRight (originComposition A f g).hom I =
    (originCompositionAmbient A f g).hom at hm
  have h := originComposition_model A f g
  rw [hm] at h
  exact congr_app h L


private theorem origin_model_word
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (originCompositionModel A f g).hom.app L =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((compactBoundary A (HasCompactification.compactification f)).hom.app L) ≫
      (compactBoundary A (HasCompactification.compactification g)).hom.app
        ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L) ≫
      (boundedSite A Z).map ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L) ≫
      (compactBoundary A (HasCompactification.compactification (f ≫ g))).inv.app L := by
  conv_lhs =>
    simp only [originCompositionModel, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.comp_map]
  exact pasted_boundary_word (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
      ((compactSupportSiteComparison A (HasCompactification.compactification f)).hom.app L)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).inv.app L))
      ((compactSupportSiteComparison A (HasCompactification.compactification g)).hom.app
        ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).inv.app
          ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L)))
      ((boundedSite A Z).map ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekPlusCompatibility
          (ModuleCat.{u + 1} A) (f ≫ g)).hom.app L))
      ((compactSupportSiteComparison A
        (HasCompactification.compactification (f ≫ g))).inv.app L)


private noncomputable def realizedEtaleCompositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f) ⋙
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (HasCompactification.compactification g) ≅
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (HasCompactification.compactification (f ≫ g)) :=
  Etale.rightDerivedLowerShriekPlusCompIso A f g

private theorem realizedEtaleRestrictionCompositor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (realizedEtaleCompositor A f g).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (Etale.compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification (f ≫ g))).hom.app L =
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (HasCompactification.compactification g)).map
        ((Etale.compactSupportCoefficientRestrictionPlus φ
          (HasCompactification.compactification f)).hom.app L) ≫
      (Etale.compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification g)).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B)
      (HasCompactification.compactification f)).obj L) ≫
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((realizedEtaleCompositor B f g).hom.app L) := by
  simpa only [realizedEtaleCompositor, Etale.rightDerivedLowerShriekPlus] using
    Etale.compactSupportRestrictionPlus_compositor φ f g L

attribute [local irreducible] realizedEtaleCompositor

private noncomputable def realizedCompositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    boundedSite A X ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f) ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification g) ≅
    boundedSite A X ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification (f ≫ g)) :=
  originCompositionModel A f g

private theorem realizedCompositor_hom_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (realizedCompositor A f g).hom.app L =
      (originCompositionAmbient A f g).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) := by
  exact (origin_model_image A f g L).symm

attribute [local irreducible] realizedCompositor

private theorem origin_model_boundary
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (realizedCompositor A f g).hom.app L =
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification g)).map
        ((compactBoundary A (HasCompactification.compactification f)).hom.app L) ≫
      (compactBoundary A (HasCompactification.compactification g)).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f)).obj L) ≫
      (boundedSite A Z).map ((realizedEtaleCompositor A f g).hom.app L) ≫
      (compactBoundary A (HasCompactification.compactification (f ≫ g))).inv.app L := by
  simpa only [realizedCompositor, realizedEtaleCompositor, rightDerivedLowerShriek,
    Etale.rightDerivedLowerShriekPlus] using origin_model_word A f g L


attribute [local irreducible] compactSupportRestrictionIso

private theorem morphism_cube
    {C : Type*} [Category C]
    {T₀ T₁ T₂ T₃ T₄ T₅ E₀ E₁ E₂ H₀ H₁ H₂ : C}
    (u : T₀ ⟶ T₁) (c : T₁ ⟶ T₂) (aA : T₀ ⟶ T₄) (aB : T₂ ⟶ T₃)
    (uH : T₄ ⟶ T₅) (cH : T₅ ⟶ T₃)
    (bFA : T₀ ⟶ E₀) (bFB : T₂ ⟶ E₁) (bHA : T₄ ≅ H₀) (bHB : T₃ ≅ H₁)
    (eA : E₀ ⟶ H₀) (eB : E₁ ⟶ H₁) (eF : E₀ ⟶ E₂) (eR : E₂ ⟶ H₂)
    (dF : E₂ ⟶ E₁) (eH : H₀ ⟶ H₂) (dH : H₂ ⟶ H₁)
    (hFG : u ≫ c ≫ bFB = bFA ≫ eF ≫ dF)
    (hH : uH ≫ cH ≫ bHB.hom = bHA.hom ≫ eH ≫ dH)
    (hEt : eA ≫ eH = eF ≫ eR) (hNat : dF ≫ eB = eR ≫ dH)
    (hmA : aA = bFA ≫ eA ≫ bHA.inv)
    (hmB : aB = bFB ≫ eB ≫ bHB.inv) :
    u ≫ c ≫ aB = aA ≫ uH ≫ cH := by
  rw [hmA, hmB]
  apply (cancel_mono bHB.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hFG, hH]
  simp only [Iso.inv_hom_id_assoc]
  rw [hNat, ← reassoc_of% hEt]

private theorem origin_fixed_cube_image
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification g)).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f)).map
          ((scalarSitePlus φ X).hom.app L)) ≫
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification g)).map
        ((compactSupportRestrictionIso φ (HasCompactification.compactification f)).hom.app
          ((boundedSite B X).obj L)) ≫
      (compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
      (HasCompactification.compactification f)).obj ((boundedSite B X).obj L)) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((realizedCompositor B f g).hom.app L)) =
    (realizedCompositor A f g).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification (f ≫ g))).map
        ((scalarSitePlus φ X).hom.app L) ≫
      (compactSupportRestrictionIso φ (HasCompactification.compactification (f ≫ g))).hom.app
        ((boundedSite B X).obj L) := by
  have hp := boundary_cube_paste
    (boundedSite A X)
    (boundedSite A Y)
    (boundedSite A Z)
    (boundedSite B X)
    (boundedSite B Y)
    (boundedSite B Z)
    ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus)
    ((Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus)
    ((Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ)
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f))
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
      (HasCompactification.compactification g))
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B)
      (HasCompactification.compactification f))
    (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B)
      (HasCompactification.compactification g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification g))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
      (HasCompactification.compactification f))
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
      (HasCompactification.compactification g))
    (scalarSitePlus φ X)
    (scalarSitePlus φ Y)
    (scalarSitePlus φ Z)
    (compactBoundary A (HasCompactification.compactification f))
    (compactBoundary A (HasCompactification.compactification g))
    (compactBoundary B (HasCompactification.compactification f))
    (compactBoundary B (HasCompactification.compactification g))
    ((Etale.compactSupportCoefficientRestrictionPlus φ (HasCompactification.compactification
      f)).hom)
    ((Etale.compactSupportCoefficientRestrictionPlus φ (HasCompactification.compactification
      g)).hom)
    ((compactSupportRestrictionIso φ (HasCompactification.compactification f)).hom)
    ((compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom)
    (compactBoundary_cube φ _)
    (compactBoundary_cube φ _)
    (L)
  have hEt := congrArg (boundedSite A Z).map
    (realizedEtaleRestrictionCompositor φ f g L)
  have hn := (scalarSitePlus φ Z).hom.naturality
    ((realizedEtaleCompositor B f g).hom.app L)
  have hmB := congrArg
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
    (origin_model_boundary B f g L)
  have h := morphism_cube
    (
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification g)).map ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (HasCompactification.compactification f)).map (((scalarSitePlus φ
        X).hom).app (L)))
    )
    (
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification g)).map (((compactSupportRestrictionIso φ
        (HasCompactification.compactification f)).hom).app ((boundedSite B X).obj (L))) ≫
        ((compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom).app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (HasCompactification.compactification f)).obj ((boundedSite B X).obj (L)))
    )
    (
      ((realizedCompositor A f g).hom).app (((Sheaf.restrictScalars X.smallEtaleTopology
        φ).mapDerivedCategoryPlus).obj (L))
    )
    (
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((realizedCompositor B f g).hom.app L)
    )
    (
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification (f ≫ g))).map (((scalarSitePlus φ X).hom).app (L))
    )
    (
      ((compactSupportRestrictionIso φ (HasCompactification.compactification (f ≫ g))).hom).app
        ((boundedSite B X).obj (L))
    )
    (
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification g)).map (((compactBoundary A
        (HasCompactification.compactification f)).hom).app (((Sheaf.restrictScalars
        X.smallEtaleTopology φ).mapDerivedCategoryPlus).obj (L))) ≫ ((compactBoundary A
        (HasCompactification.compactification g)).hom).app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
        (HasCompactification.compactification f)).obj (((Sheaf.restrictScalars X.smallEtaleTopology
        φ).mapDerivedCategoryPlus).obj (L)))
    )
    (
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (HasCompactification.compactification g)).map (((compactBoundary B
        (HasCompactification.compactification f)).hom).app (L)) ≫ ((compactBoundary B
        (HasCompactification.compactification g)).hom).app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B)
        (HasCompactification.compactification f)).obj (L)))
    )
    (
      (compactBoundary A (HasCompactification.compactification (f ≫ g))).app
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus).obj (L))
    )
    (
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).mapIso ((compactBoundary B
        (HasCompactification.compactification (f ≫ g))).app (L))
    )
    (
      (boundedSite A Z).map (((realizedEtaleCompositor A f g).hom).app (((Sheaf.restrictScalars
        X.smallEtaleTopology φ).mapDerivedCategoryPlus).obj (L)))
    )
    (
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map ((boundedSite B Z).map
        (((realizedEtaleCompositor B f g).hom).app (L)))
    )
    (
      (boundedSite A Z).map ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1}
        A) (HasCompactification.compactification g)).map
        (((Etale.compactSupportCoefficientRestrictionPlus φ (HasCompactification.compactification
        f)).hom).app (L)) ≫ ((Etale.compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification g)).hom).app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B)
        (HasCompactification.compactification f)).obj (L)))
    )
    (
      (boundedSite A Z).map (((Sheaf.restrictScalars Z.smallEtaleTopology
        φ).mapDerivedCategoryPlus).map (((realizedEtaleCompositor B f g).hom).app (L)))
    )
    (
      ((scalarSitePlus φ Z).hom).app ((Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} B) (HasCompactification.compactification g)).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B)
        (HasCompactification.compactification f)).obj (L)))
    )
    (
      (boundedSite A Z).map (((Etale.compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification (f ≫ g))).hom).app (L))
    )
    (
      ((scalarSitePlus φ Z).hom).app ((Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} B) (HasCompactification.compactification (f ≫ g))).obj (L))
    )
    (by simpa only [Category.assoc] using hp)
    (by simpa only [Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      compactBoundary_cube φ (HasCompactification.compactification (f ≫ g)) L)
    (by simpa only [Functor.map_comp, Category.assoc] using hEt)
    (by simpa only [Functor.comp_map, Functor.comp_obj] using hn.symm)
    (by
      simpa only [Category.assoc, Functor.comp_obj, Iso.app_inv] using
        (origin_model_boundary A f g
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L)))
    (by simpa only [Functor.map_comp, Functor.mapIso_inv, Iso.app_inv,
      Category.assoc] using hmB)
  simpa only [Category.assoc] using h

private theorem origin_cube_image
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((scalarSitePlus φ X).hom.app L)) ≫
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((compactSupportRestrictionIso φ (HasCompactification.compactification f)).hom.app
          ((boundedSite B X).obj L)) ≫
      (compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).obj ((boundedSite B X).obj L)) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((originCompositionAmbient B f g).hom.app
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj L))) =
    (originCompositionAmbient A f g).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
        ((scalarSitePlus φ X).hom.app L) ≫
      (compactSupportRestrictionIso φ (HasCompactification.compactification (f ≫ g))).hom.app
        ((boundedSite B X).obj L) := by
  simpa only [realizedCompositor_hom_app, rightDerivedLowerShriek, Category.assoc] using
    origin_fixed_cube_image φ f g L

private theorem origin_scalar_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((scalarSitePlus φ X).hom.app L)) ≫
      (originCompositionAmbient A f g).hom.app
        ((restrictionOrigin φ X).obj
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj L)) =
    (originCompositionAmbient A f g).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
        ((scalarSitePlus φ X).hom.app L) := by
  let v : (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ⟶
      (restrictionOrigin φ X).obj
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj L) :=
    ObjectProperty.homMk ((scalarSitePlus φ X).hom.app L)
  simpa only [Functor.comp_map, ObjectProperty.ι_map, v, ObjectProperty.homMk] using
    (originCompositionAmbient A f g).hom.naturality v

private theorem origin_restriction_image
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((compactSupportRestrictionIso φ (HasCompactification.compactification f)).hom.app
          ((boundedSite B X).obj L)) ≫
      (compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).obj ((boundedSite B X).obj L)) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((originCompositionAmbient B f g).hom.app
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj L)) =
    (originCompositionAmbient A f g).hom.app
        ((restrictionOrigin φ X).obj
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj L)) ≫
      (compactSupportRestrictionIso φ (HasCompactification.compactification (f ≫ g))).hom.app
        ((boundedSite B X).obj L) := by
  have h := origin_cube_image φ f g L
  refine transport_compositor
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((scalarSitePlus φ X).hom.app L))) _ _
    ((originCompositionAmbient A f g).hom.app
      ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L)))
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
      ((scalarSitePlus φ X).hom.app L)) _ ?_ ?_
  · simpa only [Functor.whiskerLeft_app, Category.assoc] using h
  · exact origin_scalar_naturality φ f g L

private noncomputable def restrictionCompositorSource
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).FullSubcategory ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).ι ⋙ Sheaf.derivedRestrictScalars
    (Scheme.ProEt.topology X) φ ⋙
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      g

private noncomputable def restrictionCompositorTarget
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).FullSubcategory ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).ι ⋙ rightDerivedLowerShriek
    (ModuleCat.{u + 1} B) (f ≫ g) ⋙
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ

private noncomputable def restrictionCompositorLeft
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    restrictionCompositorSource φ f g ⟶ restrictionCompositorTarget φ f g :=
  Functor.whiskerLeft (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).ι
      (Etale.pasteTwoSquaresIso
        (compactSupportRestrictionIso φ (HasCompactification.compactification f))
        (compactSupportRestrictionIso φ (HasCompactification.compactification g))).hom ≫
    Functor.whiskerRight (originCompositionAmbient B f g).hom
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ)

private theorem restrictionCompositorLeft_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).FullSubcategory) :
    (restrictionCompositorLeft φ f g).app K =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((compactSupportRestrictionIso φ (HasCompactification.compactification f)).hom.app
          K.obj) ≫
      (compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).obj K.obj) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((originCompositionAmbient B f g).hom.app K) := by
  simp only [restrictionCompositorLeft, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, ObjectProperty.ι_obj,
    Etale.pasteTwoSquaresIso_hom_app, Category.assoc, rightDerivedLowerShriek,
    Functor.comp_map, Functor.comp_obj]

private theorem restrictionCompositorLeft_app_literal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X L) :
    (restrictionCompositorLeft φ f g).app ⟨L, hL⟩ =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((compactSupportRestrictionIso φ (HasCompactification.compactification f)).hom.app
          L) ≫
      (compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).obj L) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((originCompositionAmbient B f g).hom.app ⟨L, hL⟩) := by
  simp only [restrictionCompositorLeft, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, ObjectProperty.ι_obj,
    Etale.pasteTwoSquaresIso_hom_app, Category.assoc, rightDerivedLowerShriek,
    Functor.comp_map, Functor.comp_obj]

attribute [local irreducible] restrictionCompositorLeft

private theorem restrictionCompositor_image
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (restrictionCompositorLeft φ f g).app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj K) =
      (originCompositionAmbient A f g).hom.app
        ((restrictionOrigin φ X).obj
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj K)) ≫
      (compactSupportRestrictionIso φ
        (HasCompactification.compactification (f ≫ g))).hom.app
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj K).obj := by
  rw [restrictionCompositorLeft_app]
  simpa only [boundedSite, comparisonUpperStarPlusEtaleOrigin,
    ObjectProperty.lift, Functor.comp_obj] using origin_restriction_image φ f g K

private theorem restrictionCompositorLeft_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    {K₀ K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).FullSubcategory}
    (t : K₀ ⟶ K) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map t.hom)) ≫
      (restrictionCompositorLeft φ f g).app K =
    (restrictionCompositorLeft φ f g).app K₀ ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g)).map t.hom) := by
  simpa only [restrictionCompositorSource, restrictionCompositorTarget,
    Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map] using
      (restrictionCompositorLeft φ f g).naturality t

private theorem restrictionCompositorTail_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    {L₀ L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))} (t : L₀ ⟶ L) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map t) ≫
      (compactSupportRestrictionIso φ
        (HasCompactification.compactification (f ≫ g))).hom.app L =
    (compactSupportRestrictionIso φ
      (HasCompactification.compactification (f ≫ g))).hom.app L₀ ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g)).map t) := by
  simpa only [Functor.comp_map, rightDerivedLowerShriek] using
    (compactSupportRestrictionIso φ
      (HasCompactification.compactification (f ≫ g))).hom.naturality t

private theorem origin_compositor_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    {K₀ K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory}
    (t : K₀ ⟶ K) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map t.hom) ≫
      (originCompositionAmbient A f g).hom.app K =
    (originCompositionAmbient A f g).hom.app K₀ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map t.hom := by
  simpa only [Functor.comp_map, ObjectProperty.ι_map] using
    (originCompositionAmbient A f g).hom.naturality t

private theorem restrictionCompositor_from_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X L)
    (hR : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L))
    (K₀ : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X).FullSubcategory)
    (e : K₀ ≅ ⟨L, hL⟩)
    (h₀ : (restrictionCompositorLeft φ f g).app K₀ =
      (originCompositionAmbient A f g).hom.app ((restrictionOrigin φ X).obj K₀) ≫
        (compactSupportRestrictionIso φ
          (HasCompactification.compactification (f ≫ g))).hom.app K₀.obj) :
    (restrictionCompositorLeft φ f g).app ⟨L, hL⟩ =
    (originCompositionAmbient A f g).hom.app
        ⟨(Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L, hR⟩ ≫
      (compactSupportRestrictionIso φ
        (HasCompactification.compactification (f ≫ g))).hom.app L := by
  let v : (restrictionOrigin φ X).obj K₀ ⟶
      ⟨(Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L, hR⟩ :=
    ObjectProperty.homMk
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map e.hom.hom)
  refine transport_square
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map e.hom.hom)))
    ((restrictionCompositorLeft φ f g).app K₀)
    ((restrictionCompositorLeft φ f g).app ⟨L, hL⟩)
    ((originCompositionAmbient A f g).hom.app ((restrictionOrigin φ X).obj K₀))
    ((originCompositionAmbient A f g).hom.app
      ⟨(Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L, hR⟩)
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map e.hom.hom))
    ((compactSupportRestrictionIso φ
      (HasCompactification.compactification (f ≫ g))).hom.app K₀.obj)
    ((compactSupportRestrictionIso φ
      (HasCompactification.compactification (f ≫ g))).hom.app L)
    ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) (f ≫ g)).map e.hom.hom)) ?_ ?_ ?_ ?_
  · exact restrictionCompositorLeft_naturality φ f g e.hom
  · exact h₀
  · exact restrictionCompositorTail_naturality φ f g e.hom.hom
  · simpa only [v, ObjectProperty.homMk] using origin_compositor_naturality A f g v

private theorem restrictionCompositor_at_object
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X L)
    (hR : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L)) :
    (restrictionCompositorLeft φ f g).app ⟨L, hL⟩ =
    (originCompositionAmbient A f g).hom.app
        ⟨(Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L, hR⟩ ≫
      (compactSupportRestrictionIso φ
        (HasCompactification.compactification (f ≫ g))).hom.app L := by
  obtain ⟨K₀, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X) ⟨L, hL⟩
  exact restrictionCompositor_from_iso φ f g L hL hR
    ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} B) X).obj K₀) e
    (restrictionCompositor_image φ f g K₀)

/-- Restriction of coefficients respects the canonical compositor on etale-origin objects.
Source: Stacks Project, Tags 09AF and 099R (coefficient naturality of site comparison),
0F7J and 0GL6 (proper/open composition and change of coefficients)
(blueprint: lem-sf-origin-compact-restriction-composition).

Proof: represent L by a bounded-below etale complex. The restriction of its coefficient
ring has the etale representative obtained by exact scalar restriction, as follows from
left-adjoint uniqueness for comparison pullback and restriction/coextension of scalars.
The resulting comparison is coefficient natural on sheaves: both right-adjoint routes
are the same sectionwise coextension and site restriction. Its square with geometric
inverse image commutes by conjugating to that sectionwise equality. Derive the square;
all four inverse-image and coefficient functors are exact. Taking geometric adjunction
mates gives the square with the specified proper direct-image site mate. Taking inverse
open-adjunction mates gives the square with the specified extension-by-zero site map.
Paste these two squares to obtain coefficient naturality of compactSupportSiteComparison
for each of f, g and fg. The etale restriction/compositor square is
Etale.compactSupportRestrictionPlus_compositor. Conjugate it by these three coefficient-natural
site comparisons, cancelling neighboring comparisons and inverses. By definition
originCompositionModel is precisely that conjugation. Full faithfulness of the etale-origin
equivalence identifies it with originCompositionAmbient. Finally use naturality along the
chosen realization isomorphism and its restricted image to obtain the equation for L.
All morphisms of the origin class are ambient derived morphisms, so this equation is
independent of the two retained origin witnesses. No scalar extension, tensor
presentation, constructibility or finite-Tor hypothesis is used.
-/
theorem compactSupportOriginRestrictionComposition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))
    (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} B) X L)
    (hR : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L)) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          ((compactSupportRestrictionIso φ (HasCompactification.compactification f)).hom.app L) ≫
        (compactSupportRestrictionIso φ (HasCompactification.compactification g)).hom.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).obj L) ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
          ((originCompositionAmbient B f g).hom.app ⟨L, hL⟩) =
      (originCompositionAmbient A f g).hom.app
          ⟨(Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj L, hR⟩ ≫
        (compactSupportRestrictionIso φ
          (HasCompactification.compactification (f ≫ g))).hom.app L := by
  exact (restrictionCompositorLeft_app_literal φ f g L hL).symm.trans
    (restrictionCompositor_at_object φ f g L hL hR)

end AlgebraicGeometry.ProEtale
