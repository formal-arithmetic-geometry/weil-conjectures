/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.EtaleOriginDerivedCategory
public import WeilConjectures.Compactification.RefinementCategory
/-!
# Canonical compact-support composition on the etale-origin class

Source: blueprint thm-sf-comp-composition, construction and coherence paragraphs;
Stacks Project, Tags 0F7J and 0F7K (blueprint: thm-sf-comp-composition).
The comparison is transported from the specified etale compositor. Full faithfulness
makes it natural for all ambient morphisms, independently of retained witnesses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
-- Keep the comparison models opaque while checking their coherence equations.
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [QuasiCompact f] [QuasiCompact g]

/-- Compact support restricted to the full bounded-below etale-origin class.
Source: blueprint thm-sf-comp-composition, first paragraph
(blueprint: thm-sf-comp-composition). -/
def originCompactSupport :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory ⥤
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).FullSubcategory :=
  ObjectProperty.lift _
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (fun K ↦ K.property.rightDerivedLowerShriek_obj f)

/-- The ordered etale model of the compositor, using the actual compact-support
comparison, bounded-below compatibility, and the canonical etale compositor.
Source: blueprint thm-sf-comp-composition, proof steps 2 and 7
(blueprint: thm-sf-comp-composition). -/
def originCompositionModel :
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  Functor.isoWhiskerRight (compactSupportSiteComparison A (HasCompactification.compactification f))
      (rightDerivedLowerShriek _ g) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).symm
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        rightDerivedLowerShriek _ g) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus _ f)
      (compactSupportSiteComparison A (HasCompactification.compactification g)) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus _ f)
      (Functor.isoWhiskerRight
        (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).symm
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory) ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusCompIso A f g)
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g))
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory ≪≫
    (compactSupportSiteComparison A (HasCompactification.compactification (f ≫ g))).symm

/-- Descend the specified model along the canonical etale-origin equivalence.
This preimage is unique, rather than an arbitrary choice of a natural isomorphism.
Source: blueprint thm-sf-comp-composition, witness conjugation in proof step 2
(blueprint: thm-sf-comp-composition). -/
def originCompositionAmbient :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (X := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (Y := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (originCompositionModel A f g)

/-- The canonical natural isomorphism alpha on the full origin class. Its homs are
all ambient derived morphisms, so changing or forgetting witnesses does not affect it.
Source: blueprint thm-sf-comp-composition, displayed isomorphism
(blueprint: thm-sf-comp-composition). -/
def originComposition :
    originCompactSupport A f ⋙ originCompactSupport A g ≅ originCompactSupport A (f ≫ g) :=
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  (H.whiskeringRight _).preimageIso
    (X := originCompactSupport A f ⋙ originCompactSupport A g)
    (Y := originCompactSupport A (f ≫ g)) (originCompositionAmbient A f g)

/-- Canonical identity comparison, transported from the ordinary etale identity.
Source: blueprint thm-sf-comp-composition, identity convention
(blueprint: thm-sf-comp-composition). -/
def originCompactSupportId (T : Scheme.{u}) :
    originCompactSupport A (𝟙 T) ≅ 𝟭 _ :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let model := compactSupportSiteComparison A (HasCompactification.compactification (𝟙 T)) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 T)).symm ν ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusId A T)
      (DerivedCategory.Plus.ι ⋙ ν)
  let ambient : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι :=
    (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).fullyFaithfulι
  (H.whiskeringRight _).preimageIso
    (X := originCompactSupport A (𝟙 T)) (Y := 𝟭 _) ambient

/-- Equality transport for the chosen compact-support functors.
Source: blueprint thm-sf-comp-composition, coherent identifications
(blueprint: thm-sf-comp-composition). -/
def originCompactSupportCongr {f' : X ⟶ Y} [HasCompactification f'] (h : f = f') :
    originCompactSupport A f ≅ originCompactSupport A f' :=
  h ▸ Iso.refl _

-- The site comparison with the bounded-below compatibility absorbed into it.
private def originComparisonModel :
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
        originCompactSupport A f ≅
      Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f ⋙
        comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y :=
  ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).fullyFaithfulι.whiskeringRight
    _).preimageIso
    (X := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
      originCompactSupport A f)
    (Y := Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f ⋙
      comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y)
    (compactSupportSiteComparison A (HasCompactification.compactification f) ≪≫
      Functor.isoWhiskerRight
        (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).symm
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory)

attribute [local irreducible] originCompositionModel originComparisonModel
  originCompositionAmbient originComposition originCompactSupportId

private theorem descent_app {C D E : Type*} [Category C] [Category D] [Category E]
    (Φ : C ⥤ D) (hΦ : ((Functor.whiskeringLeft C D E).obj Φ).FullyFaithful)
    {F G : D ⥤ E} (e : Φ ⋙ F ≅ Φ ⋙ G) (L : C) :
    (hΦ.preimageIso e).hom.app (Φ.obj L) = e.hom.app L := by
  exact congr_app (hΦ.map_preimage (X := F) (Y := G) e.hom) L

private theorem inclusion_app {C D E : Type*} [Category C] [Category D] [Category E]
    (H : D ⥤ E) (hH : H.FullyFaithful) {F G : C ⥤ D}
    (e : F ⋙ H ≅ G ⋙ H) (L : C) :
    H.map (((hH.whiskeringRight C).preimageIso e).hom.app L) = e.hom.app L := by
  exact congr_app ((hH.whiskeringRight C).map_preimage e.hom) L

private theorem originCompositionAmbient_app
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (originCompositionAmbient A f g).hom.app
      ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
        (originCompositionModel A f g).hom.app L := by
  unfold originCompositionAmbient
  exact descent_app _ _ (originCompositionModel A f g) L

private theorem originComposition_app
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((originComposition A f g).hom.app
      ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L)).hom =
        (originCompositionModel A f g).hom.app L := by
  rw [← originCompositionAmbient_app]
  unfold originComposition
  rfl

omit [QuasiCompact f] in
private theorem originComparisonModel_app
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((originComparisonModel A f).hom.app L).hom =
      (compactSupportSiteComparison A (HasCompactification.compactification f) ≪≫
        Functor.isoWhiskerRight
          (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).symm
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).hom.app L := by
  unfold originComparisonModel
  exact congr_app
    (((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).fullyFaithfulι.whiskeringRight
      _).map_preimage
      (X := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
        originCompactSupport A f)
      (Y := Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f ⋙
        comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y)
      (compactSupportSiteComparison A (HasCompactification.compactification f) ≪≫
        Functor.isoWhiskerRight
          (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).symm
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).hom) L

private theorem cancel_iso_hom {C : Type*} [Category C] {X Y : C} (e : X ≅ Y)
    {Z : C} {a b : Z ⟶ X} (h : a ≫ e.hom = b ≫ e.hom) : a = b := by
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using
    congrArg (fun t ↦ t ≫ e.inv) h

-- Transport the associativity diagram before specializing to derived-category functors.
private theorem transport_assoc
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {Φ₁ : C₁ ⥤ D₁} {Φ₂ : C₂ ⥤ D₂} {Φ₃ : C₃ ⥤ D₃} {Φ₄ : C₄ ⥤ D₄}
    {F₁ : D₁ ⥤ D₂} {F₂ : D₂ ⥤ D₃} {F₃ : D₃ ⥤ D₄}
    {F₁₂ : D₁ ⥤ D₃} {F₂₃ : D₂ ⥤ D₄} {Fₗ Fᵣ : D₁ ⥤ D₄}
    {G₁ : C₁ ⥤ C₂} {G₂ : C₂ ⥤ C₃} {G₃ : C₃ ⥤ C₄}
    {G₁₂ : C₁ ⥤ C₃} {G₂₃ : C₂ ⥤ C₄} {Gₗ Gᵣ : C₁ ⥤ C₄}
    (p₁ : Φ₁ ⋙ F₁ ≅ G₁ ⋙ Φ₂) (p₂ : Φ₂ ⋙ F₂ ≅ G₂ ⋙ Φ₃)
    (p₃ : Φ₃ ⋙ F₃ ≅ G₃ ⋙ Φ₄) (p₁₂ : Φ₁ ⋙ F₁₂ ≅ G₁₂ ⋙ Φ₃)
    (p₂₃ : Φ₂ ⋙ F₂₃ ≅ G₂₃ ⋙ Φ₄) (pₗ : Φ₁ ⋙ Fₗ ≅ Gₗ ⋙ Φ₄)
    (pᵣ : Φ₁ ⋙ Fᵣ ≅ Gᵣ ⋙ Φ₄)
    (a₁₂ : F₁ ⋙ F₂ ≅ F₁₂) (a₂₃ : F₂ ⋙ F₃ ≅ F₂₃)
    (aₗ : F₁₂ ⋙ F₃ ≅ Fₗ) (aᵣ : F₁ ⋙ F₂₃ ≅ Fᵣ) (e : Fₗ ≅ Fᵣ)
    (b₁₂ : G₁ ⋙ G₂ ≅ G₁₂) (b₂₃ : G₂ ⋙ G₃ ≅ G₂₃)
    (bₗ : G₁₂ ⋙ G₃ ≅ Gₗ) (bᵣ : G₁ ⋙ G₂₃ ≅ Gᵣ) (d : Gₗ ≅ Gᵣ)
    (h₁₂ : Functor.whiskerLeft Φ₁ a₁₂.hom ≫ p₁₂.hom =
      Functor.whiskerRight p₁.hom F₂ ≫ Functor.whiskerLeft G₁ p₂.hom ≫
        Functor.whiskerRight b₁₂.hom Φ₃)
    (h₂₃ : Functor.whiskerLeft Φ₂ a₂₃.hom ≫ p₂₃.hom =
      Functor.whiskerRight p₂.hom F₃ ≫ Functor.whiskerLeft G₂ p₃.hom ≫
        Functor.whiskerRight b₂₃.hom Φ₄)
    (hₗ : Functor.whiskerLeft Φ₁ aₗ.hom ≫ pₗ.hom =
      Functor.whiskerRight p₁₂.hom F₃ ≫ Functor.whiskerLeft G₁₂ p₃.hom ≫
        Functor.whiskerRight bₗ.hom Φ₄)
    (hᵣ : Functor.whiskerLeft Φ₁ aᵣ.hom ≫ pᵣ.hom =
      Functor.whiskerRight p₁.hom F₂₃ ≫ Functor.whiskerLeft G₁ p₂₃.hom ≫
        Functor.whiskerRight bᵣ.hom Φ₄)
    (hc : Functor.whiskerLeft Φ₁ e.hom ≫ pᵣ.hom =
      pₗ.hom ≫ Functor.whiskerRight d.hom Φ₄)
    (he : Functor.whiskerRight b₁₂.hom G₃ ≫ bₗ.hom ≫ d.hom =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft G₁ b₂₃.hom ≫ bᵣ.hom) :
    Functor.whiskerLeft Φ₁ (Functor.whiskerRight a₁₂.hom F₃ ≫ aₗ.hom ≫ e.hom) =
      Functor.whiskerLeft Φ₁ ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft F₁ a₂₃.hom ≫ aᵣ.hom) := by
  apply NatTrans.ext
  funext L
  apply cancel_iso_hom (pᵣ.app L)
  simp only [Iso.app_hom]
  have hw := congr_app hc L
  have hfg := congr_app h₁₂ L
  have hfgh := congr_app hₗ L
  have hfgh' := congr_app hᵣ L
  have hgh := congr_app h₂₃ (G₁.obj L)
  have hn := a₂₃.hom.naturality (p₁.hom.app L)
  have hn' := p₃.hom.naturality (b₁₂.hom.app L)
  have he' := congr_app he L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.comp_map] at hw hfg hfgh hfgh' hgh hn hn' he' ⊢
  simp only [Category.assoc, hw, reassoc_of% hfgh, reassoc_of% hfgh']
  rw [← Functor.map_comp_assoc, hfg, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn']
  have hem := congrArg (fun t ↦ Φ₄.map t) he'
  simp only [Functor.map_comp] at hem
  rw [hem]
  rw [← reassoc_of% hgh, reassoc_of% hn]
  rw [hfgh']

private theorem originComposition_model :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
        (originComposition A f g).hom ≫ (originComparisonModel A (f ≫ g)).hom =
      Functor.whiskerRight (originComparisonModel A f).hom (originCompactSupport A g) ≫
        Functor.whiskerLeft (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
          (originComparisonModel A g).hom ≫
        Functor.whiskerRight (Etale.rightDerivedLowerShriekPlusCompIso A f g).hom
          (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Z)  := by
  ext L
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, originComposition_app,
    originComparisonModel_app]
  set_option backward.isDefEq.respectTransparency false in
  simp only [originCompositionModel, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    originCompactSupport, ObjectProperty.lift_map, ObjectProperty.FullSubcategory.comp_hom,
    Functor.comp_map, ObjectProperty.ι_map, Functor.map_comp,
    comparisonUpperStarPlusEtaleOrigin, ObjectProperty.homMk, Functor.comp_obj,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id]
  simp only [ObjectProperty.homMk, originComparisonModel_app, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, Category.comp_id]
  dsimp only [originCompactSupport, comparisonUpperStarPlusEtaleOrigin,
    ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [Functor.map_id, Category.comp_id]

omit [QuasiCompact f] in
private theorem originCompactSupportCongr_model {f' : X ⟶ Y} [HasCompactification f']
    (w : f = f') :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
        (originCompactSupportCongr A f w).hom ≫ (originComparisonModel A f').hom =
      (originComparisonModel A f).hom ≫
        Functor.whiskerRight (Etale.rightDerivedLowerShriekPlusCongr A w).hom
          (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) Y) := by
  subst f'
  change Functor.whiskerLeft _ (𝟙 (originCompactSupport A f)) ≫
      (originComparisonModel A f).hom =
    (originComparisonModel A f).hom ≫
      Functor.whiskerRight (𝟙 (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)) _
  simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.id_comp,
    Category.comp_id]

private theorem originCompactSupportId_model (T : Scheme.{u}) :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T)
        (originCompactSupportId A T).hom =
      (originComparisonModel A (𝟙 T)).hom ≫
        Functor.whiskerRight (Etale.rightDerivedLowerShriekPlusId A T).hom
          (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T) := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let model := compactSupportSiteComparison A (HasCompactification.compactification (𝟙 T)) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 T)).symm ν ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusId A T)
      (DerivedCategory.Plus.ι ⋙ ν)
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).fullyFaithfulι
  let ambient : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T) ≅
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι :=
    Φ.asEquivalence.congrLeft.fullyFaithfulInverse.preimageIso model
  ext L
  have h₁ := inclusion_app _ H
    (F := originCompactSupport A (𝟙 T)) (G := 𝟭 _) ambient (Φ.obj L)
  have h₂ := descent_app Φ Φ.asEquivalence.congrLeft.fullyFaithfulInverse
    (F := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T))
    (G := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι) model L
  simp only [H, originCompactSupport, ObjectProperty.ι_map,
    Functor.comp_obj, ObjectProperty.ι_obj] at h₁
  have he : ((originCompactSupportId A T).hom.app (Φ.obj L)).hom = model.hom.app L :=
    by
      set_option backward.isDefEq.respectTransparency false in
        simpa only [originCompactSupportId, ambient, H, Φ, model, ν] using h₁.trans h₂
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ObjectProperty.FullSubcategory.comp_hom]
  rw [he]
  set_option backward.isDefEq.respectTransparency false in
  simp only [model, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, originComparisonModel_app, Functor.comp_map,
    ObjectProperty.ι_map, Category.assoc, ν, comparisonUpperStarPlusEtaleOrigin,
    ObjectProperty.lift_map, ObjectProperty.homMk, Functor.comp_map]

attribute [local irreducible] originCompactSupport originCompactSupportCongr

/-- The canonical compositor is the identity when its first morphism is an identity.
Source: blueprint thm-sf-comp-composition, unit clause
(blueprint: thm-sf-comp-composition).
Proof: precompose with the etale-origin equivalence, substitute the defining model,
and cancel inverse comparison maps. The equation becomes the ordinary etale unit law.
Full faithfulness then reflects the equality; all ambient morphisms are retained. -/
theorem originComposition_id_left [HasCompactification (𝟙 X ≫ f)] :
    (originComposition A (𝟙 X) f).hom =
      Functor.whiskerRight (originCompactSupportId A X).hom _ ≫
        (Functor.leftUnitor _).hom ≫
          (originCompactSupportCongr A f (Category.id_comp f).symm).hom := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  apply Φ.asEquivalence.congrLeft.fullyFaithfulInverse.map_injective
  change Functor.whiskerLeft Φ _ = Functor.whiskerLeft Φ _
  apply (cancel_mono (originComparisonModel A (𝟙 X ≫ f)).hom).1
  rw [originComposition_model]
  apply NatTrans.ext
  funext L
  have hw := congr_app
    (originCompactSupportCongr_model A f (Category.id_comp f).symm) L
  have hu := congr_app (originCompactSupportId_model A X) L
  have hn := (originComparisonModel A f).hom.naturality
    ((Etale.rightDerivedLowerShriekPlusId A X).hom.app L)
  have he := congr_app (Etale.rightDerivedLowerShriekPlusCompIso_id_left A f) L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id] at hw hu hn he ⊢
  simp only [Φ, Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Category.id_comp, Category.comp_id, Category.assoc] at hw hu hn he ⊢
  simp only [he, Functor.map_comp, Category.assoc, hu, hw]
  rw [reassoc_of% hn]

/-- The canonical compositor is the identity when its second morphism is an identity.
Source: blueprint thm-sf-comp-composition, unit clause
(blueprint: thm-sf-comp-composition).
Proof: expand the model after precomposition with the comparison equivalence. Cancel
adjacent comparisons, apply the etale right-unit equation, and reflect equality by
full faithfulness. This is independent of any choice of etale-origin witness. -/
theorem originComposition_id_right [HasCompactification (f ≫ 𝟙 Y)] :
    (originComposition A f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (originCompactSupportId A Y).hom ≫
        (Functor.rightUnitor _).hom ≫
          (originCompactSupportCongr A f (Category.comp_id f).symm).hom := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  apply Φ.asEquivalence.congrLeft.fullyFaithfulInverse.map_injective
  change Functor.whiskerLeft Φ _ = Functor.whiskerLeft Φ _
  apply (cancel_mono (originComparisonModel A (f ≫ 𝟙 Y)).hom).1
  rw [originComposition_model]
  apply NatTrans.ext
  funext L
  have hw := congr_app
    (originCompactSupportCongr_model A f (Category.comp_id f).symm) L
  have hu := congr_app (originCompactSupportId_model A Y)
    ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L)
  have hn := (originCompactSupportId A Y).hom.naturality
    ((originComparisonModel A f).hom.app L)
  have he := congr_app (Etale.rightDerivedLowerShriekPlusCompIso_id_right A f) L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id] at hw hu hn he ⊢
  simp only [Φ, Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Category.id_comp, Category.comp_id, Category.assoc] at hw hu hn he ⊢
  simp only [he, Functor.map_comp, Category.assoc, hw]
  rw [← reassoc_of% hu, reassoc_of% hn]

/-- Associativity with the specified associator and equality transport.
Source: blueprint thm-sf-comp-composition, associativity clause
(blueprint: thm-sf-comp-composition).
Proof: expand every model after the fully faithful etale-origin equivalence.
Comparison composition coherence cancels the intermediate site comparisons. Both
remaining expressions are the etale associativity equation, conjugated by the same
end comparisons. Reflect the equality using full faithfulness. -/
theorem originComposition_assoc {T : Scheme.{u}} (h : Z ⟶ T)
    [HasCompactification h] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)]
    [QuasiCompact h] :
    Functor.whiskerRight (originComposition A f g).hom (originCompactSupport A h) ≫
        (originComposition A (f ≫ g) h).hom ≫
        (originCompactSupportCongr A ((f ≫ g) ≫ h) (Category.assoc f g h)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (originCompactSupport A f) (originComposition A g h).hom ≫
          (originComposition A f (g ≫ h)).hom := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  apply Φ.asEquivalence.congrLeft.fullyFaithfulInverse.map_injective
  change Functor.whiskerLeft Φ _ = Functor.whiskerLeft Φ _
  exact transport_assoc
    (originComparisonModel A f) (originComparisonModel A g) (originComparisonModel A h)
    (originComparisonModel A (f ≫ g)) (originComparisonModel A (g ≫ h))
    (originComparisonModel A ((f ≫ g) ≫ h)) (originComparisonModel A (f ≫ g ≫ h))
    (originComposition A f g) (originComposition A g h)
    (originComposition A (f ≫ g) h) (originComposition A f (g ≫ h))
    (originCompactSupportCongr A ((f ≫ g) ≫ h) (Category.assoc f g h))
    (Etale.rightDerivedLowerShriekPlusCompIso A f g)
    (Etale.rightDerivedLowerShriekPlusCompIso A g h)
    (Etale.rightDerivedLowerShriekPlusCompIso A (f ≫ g) h)
    (Etale.rightDerivedLowerShriekPlusCompIso A f (g ≫ h))
    (Etale.rightDerivedLowerShriekPlusCongr A (Category.assoc f g h))
    (originComposition_model A f g) (originComposition_model A g h)
    (originComposition_model A (f ≫ g) h) (originComposition_model A f (g ≫ h))
    (originCompactSupportCongr_model A ((f ≫ g) ≫ h) (Category.assoc f g h))
    (Etale.rightDerivedLowerShriekPlusCompIso_assoc A f g h)

/-- The canonical fixed-scalar presentation of a retained origin witness.
Source: blueprint thm-sf-comp-composition, witnessed domain
(blueprint: thm-sf-comp-composition). -/
def originWitnessFixedAmbient (T : Scheme.{u})
    [TopologicalSpace A] [DiscreteTopology A] :
    EtaleOriginDerivedCategory T A ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  letI : (finiteCoefficientRealization T A).asEquivalence.inverse.Additive :=
    @Equivalence.inverse_additive _ _ _ _ _ _
      (finiteCoefficientRealization T A).asEquivalence
        (finiteCoefficientRealization_additive T A)
  etaleOriginForgetful T A ⋙
    (finiteCoefficientRealization T A).asEquivalence.inverse.mapDerivedCategory

/-- The retained etale witness remains an origin witness after the canonical
coefficient equivalence; this supplies the full-subcategory lift.
Source: blueprint thm-sf-comp-composition, coefficient transport
(blueprint: thm-sf-comp-composition).
Proof: apply the exact inverse coefficient equivalence to the retained alpha.
The unit of that equivalence identifies its composite with coefficient realization
with the identity. The resulting alpha is precisely an isomorphism from the
comparison inverse image of the same bounded-below etale L to the transported K. -/
theorem originWitnessFixed_property (T : Scheme.{u})
    [TopologicalSpace A] [DiscreteTopology A] (K : EtaleOriginDerivedCategory T A) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T
      ((originWitnessFixedAmbient A T).obj K) := by
  let E := (finiteCoefficientRealization T A).asEquivalence
  let : E.functor.Additive := finiteCoefficientRealization_additive T A
  let : E.inverse.Additive :=
    @Equivalence.inverse_additive _ _ _ _ _ _ E
      (finiteCoefficientRealization_additive T A)
  let L := K.2.L
  let ν := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let e : (finiteCoefficientComparison T A).mapDerivedCategory.obj L.obj ≅ K.1.obj :=
    ((finiteCoefficientComparison T A).mapDerivedCategoryPlusCompatibility.app L).symm ≪≫
      DerivedCategory.Plus.ι.mapIso K.2.alpha
  refine ⟨L.obj, L.property, ⟨?_⟩⟩
  exact E.mapDerivedCategory.unitIso.app (ν.mapDerivedCategory.obj L.obj) ≪≫
    E.inverse.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryCompIso ν (finiteCoefficientRealization T A)).symm.app
        L.obj ≪≫ e)

/-- Forget the witness after canonical coefficient transport, without discarding any
ambient morphisms. Source: blueprint thm-sf-comp-composition, witnessed domain
(blueprint: thm-sf-comp-composition). -/
def originWitnessFixed (T : Scheme.{u}) [TopologicalSpace A] [DiscreteTopology A] :=
  ObjectProperty.lift _ (originWitnessFixedAmbient A T)
    (fun K ↦ originWitnessFixed_property A T K)

/-- Alpha on the recorded witness-retaining category. Its components are the same
ambient alpha components, so the identity between two witnesses identifies them.
Source: blueprint thm-sf-comp-composition, independence of the witness
(blueprint: thm-sf-comp-composition). -/
def originCompositionWitnessed [TopologicalSpace A] [DiscreteTopology A] :=
  Functor.isoWhiskerLeft (originWitnessFixed A X) (originCompositionAmbient A f g)

end AlgebraicGeometry.ProEtale
