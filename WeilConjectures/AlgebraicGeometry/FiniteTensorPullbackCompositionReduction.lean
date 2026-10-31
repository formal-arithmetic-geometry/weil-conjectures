/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteTensorFixedComparisons
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.FiniteIntrinsicPullbackUnitComposition
import all WeilConjectures.SixFunctors.ScalarPullbackCompositionCoherence
import all WeilConjectures.AlgebraicGeometry.IntrinsicConjugateComparisonTransport
import all WeilConjectures.AlgebraicGeometry.FiniteDirectCounitFixedRealizationTransport
import all WeilConjectures.AlgebraicGeometry.PurityFiniteSetting

/-! # Finite coefficient pullback coherence in fixed-scalar coordinates


Source: the finite-reduction proof Step 2, expanded presentation-reduction Step 7;
Stacks Project, sites-cohomology.tex, Tag 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

attribute [local instance 100000] proEtaleRingModules_hasDerivedCategory
attribute [local instance 200000] SheafOfModules.instAbelian
private noncomputable local instance (priority := 200000) finiteTensorFixedStalk (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} _


section Coordinates
variable {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]

private theorem scalar_coordinates_comp
    (E₀ : A₀ ⥤ C₀) (E₁ : A₁ ⥤ C₁) (E₂ : A₂ ⥤ C₂)
    (J₀ : B₀ ⥤ D₀) (J₁ : B₁ ⥤ D₁) (J₂ : B₂ ⥤ D₂) [J₂.Faithful]
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (H : A₀ ⥤ A₂)
    (f : C₀ ⥤ C₁) (g : C₁ ⥤ C₂) (h : C₀ ⥤ C₂)
    (F' : B₀ ⥤ B₁) (G' : B₁ ⥤ B₂) (H' : B₀ ⥤ B₂)
    (f' : D₀ ⥤ D₁) (g' : D₁ ⥤ D₂) (h' : D₀ ⥤ D₂)
    (Q₀ : A₀ ⥤ B₀) (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂)
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂)
    (s₀ : E₀ ⋙ R₀ ≅ Q₀ ⋙ J₀) (s₁ : E₁ ⋙ R₁ ≅ Q₁ ⋙ J₁)
    (s₂ : E₂ ⋙ R₂ ≅ Q₂ ⋙ J₂)
    (qF : E₀ ⋙ f ≅ F ⋙ E₁) (qG : E₁ ⋙ g ≅ G ⋙ E₂)
    (qH : E₀ ⋙ h ≅ H ⋙ E₂)
    (qF' : J₀ ⋙ f' ≅ F' ⋙ J₁) (qG' : J₁ ⋙ g' ≅ G' ⋙ J₂)
    (qH' : J₀ ⋙ h' ≅ H' ⋙ J₂)
    (tF : f ⋙ R₁ ≅ R₀ ⋙ f') (tG : g ⋙ R₂ ≅ R₁ ⋙ g')
    (tH : h ⋙ R₂ ≅ R₀ ⋙ h')
    (a : H ≅ F ⋙ G) (a' : H' ≅ F' ⋙ G')
    (b : h ≅ f ⋙ g) (b' : h' ≅ f' ⋙ g')
    (cF : ∀ K, Q₁.obj (F.obj K) ≅ F'.obj (Q₀.obj K))
    (cG : ∀ K, Q₂.obj (G.obj K) ≅ G'.obj (Q₁.obj K))
    (cH : ∀ K, Q₂.obj (H.obj K) ≅ H'.obj (Q₀.obj K))
    (ha : ∀ K, qH.hom.app K ≫ E₂.map (a.hom.app K) =
      b.hom.app (E₀.obj K) ≫ g.map (qF.hom.app K) ≫ qG.hom.app (F.obj K))
    (hb : ∀ K, qH'.hom.app K ≫ J₂.map (a'.hom.app K) =
      b'.hom.app (J₀.obj K) ≫ g'.map (qF'.hom.app K) ≫ qG'.hom.app (F'.obj K))
    (ht : ∀ K, R₂.map (b.hom.app K) ≫ tG.hom.app (f.obj K) ≫
      g'.map (tF.hom.app K) = tH.hom.app K ≫ b'.hom.app (R₀.obj K))
    (hcF : ∀ K, R₁.map (qF.hom.app K) ≫ s₁.hom.app (F.obj K) ≫
      J₁.map (cF K).hom = tF.hom.app (E₀.obj K) ≫
      f'.map (s₀.hom.app K) ≫ qF'.hom.app (Q₀.obj K))
    (hcG : ∀ K, R₂.map (qG.hom.app K) ≫ s₂.hom.app (G.obj K) ≫
      J₂.map (cG K).hom = tG.hom.app (E₁.obj K) ≫
      g'.map (s₁.hom.app K) ≫ qG'.hom.app (Q₁.obj K))
    (hcH : ∀ K, R₂.map (qH.hom.app K) ≫ s₂.hom.app (H.obj K) ≫
      J₂.map (cH K).hom = tH.hom.app (E₀.obj K) ≫
      h'.map (s₀.hom.app K) ≫ qH'.hom.app (Q₀.obj K))
    (K : A₀) :
    Q₂.map (a.hom.app K) ≫ (cG (F.obj K)).hom ≫ G'.map (cF K).hom =
      (cH K).hom ≫ a'.hom.app (Q₀.obj K) := by
  apply J₂.map_injective
  simp only [Functor.map_comp]
  apply (cancel_epi (R₂.map (qH.hom.app K) ≫ s₂.hom.app (H.obj K))).mp
  simp only [Category.assoc]
  rw [← reassoc_of% (s₂.hom.naturality (a.hom.app K))]
  rw [← R₂.map_comp_assoc, ha K]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hcG (F.obj K))]
  have hqn := qG'.hom.naturality (cF K).hom
  dsimp only [Functor.comp_map] at hqn
  rw [← hqn]
  have htn := tG.hom.naturality (qF.hom.app K)
  dsimp only [Functor.comp_map] at htn
  rw [reassoc_of% htn]
  rw [← g'.map_comp_assoc, ← g'.map_comp_assoc]
  simp only [Category.assoc]
  rw [hcF K]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (ht (E₀.obj K))]
  rw [reassoc_of% (hcH K)]
  have hbn := b'.hom.naturality (s₀.hom.app K)
  dsimp only [Functor.comp_map] at hbn
  rw [← reassoc_of% hbn]
  rw [← hb (Q₀.obj K)]

private theorem compose_coordinate_models
    {A₀ A₁ A₂ A₀' A₁' A₂' : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category A₀'] [Category A₁'] [Category A₂']
    (E₀ : A₀ ⥤ A₀') (E₁ : A₁ ⥤ A₁') (E₂ : A₂ ⥤ A₂')
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (H : A₀ ⥤ A₂)
    (f gF : A₀' ⥤ A₁') (g gG : A₁' ⥤ A₂') (h gH : A₀' ⥤ A₂')
    (qF : F ⋙ E₁ ≅ E₀ ⋙ f) (qG : G ⋙ E₂ ≅ E₁ ⋙ g)
    (qH : H ⋙ E₂ ≅ E₀ ⋙ h)
    (eF : gF ≅ f) (eG : gG ≅ g) (eH : gH ≅ h)
    (a : H ≅ F ⋙ G) (b : h ≅ f ⋙ g) (c : gH ≅ gF ⋙ gG)
    (hq : ∀ K, E₂.map (a.hom.app K) ≫ qG.hom.app (F.obj K) ≫
      g.map (qF.hom.app K) = qH.hom.app K ≫ b.hom.app (E₀.obj K))
    (he : ∀ K, c.hom.app K ≫ gG.map (eF.hom.app K) ≫ eG.hom.app (f.obj K) =
      eH.hom.app K ≫ b.hom.app K)
    (K : A₀) :
    eH.hom.app (E₀.obj K) ≫ qH.inv.app K ≫ E₂.map (a.hom.app K) =
      c.hom.app (E₀.obj K) ≫ gG.map (eF.hom.app (E₀.obj K) ≫ qF.inv.app K) ≫
        eG.hom.app (E₁.obj (F.obj K)) ≫ qG.inv.app (F.obj K) := by
  have ht : qH.inv.app K ≫ E₂.map (a.hom.app K) =
      b.hom.app (E₀.obj K) ≫ g.map (qF.inv.app K) ≫ qG.inv.app (F.obj K) := by
    apply (cancel_epi (qH.hom.app K)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% (hq K)]
    simp only [← g.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.id_comp, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  rw [ht]
  rw [← Category.assoc, ← he (E₀.obj K)]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (eG.hom.naturality (qF.inv.app K))]

end Coordinates

section Presentation
open CategoryTheory.Limits
attribute [local implicit_reducible] Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [dC : HasDerivedCategory C] [dD : HasDerivedCategory D]
  [dE : HasDerivedCategory E] [dF : HasDerivedCategory F]

private theorem presentation_unit (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (L : C ⥤ E) (G : E ⥤ F) [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompIso (e.inverse ⋙ L) G ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso e.inverse L)
        G.mapDerivedCategory).hom.app
        (e.functor.mapDerivedCategory.obj K) ≫
      (L.mapDerivedCategory ⋙ G.mapDerivedCategory).map
        (e.mapDerivedCategory.unitIso.inv.app K) =
      (Functor.mapDerivedCategorySquareIso (e.funInvIdAssoc (L ⋙ G)).symm).inv.app K := by
  have ha :
      ((Functor.mapDerivedCategoryCompIso e.inverse (L ⋙ G)) ≪≫
        Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso L G)).hom =
      (Functor.mapDerivedCategoryCompIso (e.inverse ⋙ L) G ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso e.inverse L)
          G.mapDerivedCategory).hom := by
    simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom] using
        Functor.mapDerivedCategoryCompIso_assoc e.inverse L G
  rw [← ha]
  let q := Functor.mapDerivedCategorySquareIso (e.funInvIdAssoc (L ⋙ G)).symm
  apply (cancel_mono (q.hom.app K)).mp
  change _ = q.inv.app K ≫ q.hom.app K
  rw [Iso.inv_hom_id_app, Category.assoc]
  erw [q.hom.naturality]
  rw [← Category.assoc, derived_square_coherence e L G]
  dsimp only [Functor.comp_map]
  erw [e.mapDerivedCategory.counitInv_app_functor]
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

end Presentation

namespace AlgebraicGeometry.Scheme
open CategoryTheory.Limits
open Opposite
open ProEtale.OpenScalarTensor
attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] MorphismProperty Scheme.ProEt Scheme.instCategoryProEt
  Category.opposite CategoryStruct.opposite Quiver.opposite

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem pullbackModel_unit (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEt)
    (s : M.val.obj (op V)) :
    ((openSquarePullbackModel A f).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj V))
        (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (op V) s) =
      ((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app (op V) s :=
  (openSquarePullbackModel_existsUnique A f).exists.choose_spec M V s

set_option maxHeartbeats 2000000 in
-- Keep the ordinary adjunction models intact while comparing their sectionwise units.
private theorem pullbackModel_comp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    openSquarePullbackModel A (f ≫ g) ≪≫ sfIntrinsicPullbackComp A f g =
      ordinaryComp f g A ≪≫
        Functor.isoWhiskerRight (openSquarePullbackModel A g)
          (proEtaleConstantRingPullback A f) ≪≫
        Functor.isoWhiskerLeft (sfIntrinsicPullback A g) (openSquarePullbackModel A f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((proEtaleConstantRingAdjunction A (f ≫ g)).homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app]
  change ((sfIntrinsicPullbackComp A f g).hom.app M).val.app _
      (((openSquarePullbackModel A (f ≫ g)).hom.app M).val.app _
        (((proEtaleConstantRingAdjunction A (f ≫ g)).unit.app M).val.app V s)) = _
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs => erw [directImage_map_apply (f ≫ g) A]
  change _ = ((openSquarePullbackModel A f).hom.app
      ((sfIntrinsicPullback A g).obj M)).val.app
      (op ((proEtaleBaseChange (f ≫ g)).obj V.unop))
      ((((proEtaleConstantRingPullback A f).map
        ((openSquarePullbackModel A g).hom.app M)).val.app
          (op ((proEtaleBaseChange (f ≫ g)).obj V.unop)))
        ((((ordinaryComp f g A).hom.app M).val.app
          (op ((proEtaleBaseChange (f ≫ g)).obj V.unop)))
          (((proEtaleConstantRingAdjunction A (f ≫ g)).unit.app M).val.app V s)))
  erw [pullbackModel_unit A (f ≫ g) M V.unop s]
  erw [finiteIntrinsicPullback_unit_comp A g f M V.unop s]
  erw [ordinaryComp_unit_section f g A M V.unop s]
  erw [PresheafOfModules.naturality_apply
    (((proEtaleConstantRingPullback A f).map
      ((openSquarePullbackModel A g).hom.app M)).val)
    (((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).op)]
  erw [PresheafOfModules.naturality_apply
    (((openSquarePullbackModel A f).hom.app ((sfIntrinsicPullback A g).obj M)).val)
    (((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).op)]
  have hn₂ := (proEtaleConstantRingAdjunction A f).unit.naturality
    ((openSquarePullbackModel A g).hom.app M)
  have hv₂ := congrArg (fun t ↦ t.val.app (op ((proEtaleBaseChange g).obj V.unop))
    (((proEtaleConstantRingAdjunction A g).unit.app M).val.app V s)) hn₂
  change ((proEtaleConstantRingAdjunction A f).unit.app
      ((sfIntrinsicPullback A g).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V.unop))
        (((openSquarePullbackModel A g).hom.app M).val.app
          (op ((proEtaleBaseChange g).obj V.unop))
          (((proEtaleConstantRingAdjunction A g).unit.app M).val.app V s)) =
    ((proEtaleConstantRingPullback A f).map
      ((openSquarePullbackModel A g).hom.app M)).val.app
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj V.unop)))
        (((proEtaleConstantRingAdjunction A f).unit.app
          ((proEtaleConstantRingPullback A g).obj M)).val.app
            (op ((proEtaleBaseChange g).obj V.unop))
            (((proEtaleConstantRingAdjunction A g).unit.app M).val.app V s)) at hv₂
  erw [← hv₂, pullbackModel_unit A f ((sfIntrinsicPullback A g).obj M)
    ((proEtaleBaseChange g).obj V.unop), pullbackModel_unit A g M V.unop s]

private theorem derivedPullbackModel_comp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : proEtaleDerivedCategory Z A) :
    (openSquareDerivedPullbackModel A (f ≫ g)).hom.app K ≫
      (sfIntrinsicDerivedPullbackComp A f g).hom.app K =
    (proEtaleConstantRingPullbackComposition f g A).inv.app K ≫
      (proEtaleConstantRingDerivedPullback A f).map
        ((openSquareDerivedPullbackModel A g).hom.app K) ≫
      (openSquareDerivedPullbackModel A f).hom.app
        ((sfIntrinsicDerivedPullback A g).obj K) := by
  have h := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K)
    (pullbackModel_comp A f g)
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at h
  have hr := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight
    (openSquarePullbackModel A g) (proEtaleConstantRingPullback A f)) K
  have hl := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft
    (sfIntrinsicPullback A g) (openSquarePullbackModel A f)) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hr hl
  have ht := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryCompIso (sfIntrinsicPullback A g)
      (sfIntrinsicPullback A f)).hom.app K) h
  simp only [Category.assoc] at ht
  rw [hl, reassoc_of% hr] at ht
  have hc := congrArg (fun e ↦ e.hom.app K) (constantComparison_eq f g A)
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom] at hc
  simp only [openSquareDerivedPullbackModel, sfIntrinsicDerivedPullbackComp,
    Iso.trans_hom, NatTrans.comp_app]
  rw [hc]
  simpa only [Category.assoc] using ht

attribute [local irreducible] Functor.mapDerivedCategory
attribute [local implicit_reducible] sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory
  CategoryTheory.Equivalence.mk

private def exactRealizationSquare (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.sfFixedDerivedPullback A f ⋙ (sfIntrinsicDerivedEquivalence X A).functor ≅
      (sfIntrinsicDerivedEquivalence Y A).functor ⋙ sfIntrinsicDerivedPullback A f :=
  Functor.mapDerivedCategorySquareIso
    ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f ⋙
        (sfIntrinsicModuleEquivalence X A).functor)).symm

private def rawRealizationSquare (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicDerivedEquivalence Y A).functor ⋙ proEtaleConstantRingDerivedPullback A f ≅
      ProEtale.sfFixedDerivedPullback A f ⋙ (sfIntrinsicDerivedEquivalence X A).functor :=
  Functor.isoWhiskerLeft _ (openSquareDerivedPullbackModel A f) ≪≫
    (exactRealizationSquare A f).symm

private theorem rawRealizationSquare_comp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory (Sheaf (ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (rawRealizationSquare A (f ≫ g)).hom.app K ≫
      (sfIntrinsicDerivedEquivalence X A).functor.map
        ((WeilConjectures.PurityFiniteSetting.compositionFixedPullbackComp A f g).hom.app K) =
    (proEtaleConstantRingPullbackComposition f g A).inv.app
        ((sfIntrinsicDerivedEquivalence Z A).functor.obj K) ≫
      (proEtaleConstantRingDerivedPullback A f).map
        ((rawRealizationSquare A g).hom.app K) ≫
      (rawRealizationSquare A f).hom.app ((ProEtale.sfFixedDerivedPullback A g).obj K) := by
  have hc := (WeilConjectures.PurityFiniteSetting.existsUnique_compositionFixedPullbackComp
    A f g).choose_spec.1
  have hc' :
      WeilConjectures.PurityFiniteSetting.compositionFixedPullbackComp A f g =
        WeilConjectures.PurityFiniteSetting.compositionPullbackComp
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g := eq_of_heq hc
  rw [hc']
  simpa only [rawRealizationSquare, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
    using compose_coordinate_models
    (sfIntrinsicDerivedEquivalence Z A).functor
    (sfIntrinsicDerivedEquivalence Y A).functor
    (sfIntrinsicDerivedEquivalence X A).functor
    (ProEtale.sfFixedDerivedPullback A g) (ProEtale.sfFixedDerivedPullback A f)
    (ProEtale.sfFixedDerivedPullback A (f ≫ g))
    (sfIntrinsicDerivedPullback A g) (proEtaleConstantRingDerivedPullback A g)
    (sfIntrinsicDerivedPullback A f) (proEtaleConstantRingDerivedPullback A f)
    (sfIntrinsicDerivedPullback A (f ≫ g)) (proEtaleConstantRingDerivedPullback A (f ≫ g))
    (exactRealizationSquare A g) (exactRealizationSquare A f)
    (exactRealizationSquare A (f ≫ g))
    (openSquareDerivedPullbackModel A g) (openSquareDerivedPullbackModel A f)
    (openSquareDerivedPullbackModel A (f ≫ g))
    (WeilConjectures.PurityFiniteSetting.compositionPullbackComp
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g)
    (sfIntrinsicDerivedPullbackComp A f g)
    (proEtaleConstantRingPullbackComposition f g A).symm
    (derived_pullback_compositor_square A f g)
    (fun N ↦ (derivedPullbackModel_comp A f g N).symm) K

private theorem scalar_pullback_comp {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : proEtaleDerivedCategory Z A) :
    (ProEtale.scalarExtension φ X).map
        ((proEtaleConstantRingPullbackComposition f g A).inv.app K) ≫
      (ProEtale.tensorPullbackIso φ f).inv.app
        ((proEtaleConstantRingDerivedPullback A g).obj K) ≫
      (proEtaleConstantRingDerivedPullback B f).map
        ((ProEtale.tensorPullbackIso φ g).inv.app K) =
    (ProEtale.tensorPullbackIso φ (f ≫ g)).inv.app K ≫
      (proEtaleConstantRingPullbackComposition f g B).inv.app
        ((ProEtale.scalarExtension φ Z).obj K) := by
  have h := ProEtale.OpenScalarTensor.published_composition f g φ K
  have h' := congrArg (fun t ↦
    (ProEtale.scalarExtension φ X).map
      ((proEtaleConstantRingPullbackComposition f g A).inv.app K) ≫ t ≫
        (proEtaleConstantRingPullbackComposition f g B).inv.app
          ((ProEtale.scalarExtension φ Z).obj K)) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app] at h'
  erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp] at h'
  exact h'.symm

end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

-- Expose the cached ring operations to compare them with the canonical ULift instance.
set_option linter.auxLemma false in
attribute [local implicit_reducible] coefficientCommRing._aux_1 coefficientCommRing._aux_4
  coefficientCommRing._aux_8 coefficientCommRing._aux_13 coefficientCommRing._aux_16
  coefficientCommRing._aux_20 coefficientCommRing._aux_28 coefficientCommRing._aux_30
  coefficientCommRing._aux_32 coefficientCommRing._aux_34 coefficientCommRing._aux_41
  ULift.ring
attribute [local implicit_reducible] Coefficient coefficientCommRing
  sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence
  finiteReductionRawPullbackModel
attribute [local implicit_reducible] smoothPurityPullback finiteReductionPullback
  finiteTensorPullbackModel finiteTensorReduction sfIntrinsicPullback sfIntrinsicTransport
open CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

set_option maxHeartbeats 2000000 in
-- Normalize the coefficient alias before comparing the two realization presentations.
private theorem rawRealizationSquare_model (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteReductionRawPullbackModel f).hom.app
        ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K) ≫
      (P.finiteTensorPullbackModel f K).hom =
    (rawRealizationSquare P.Ring f).hom.app K := by
  dsimp (config := { instances := true }) only [Coefficient, coefficientCommRing] at K ⊢
  let dY : HasDerivedCategory.{u + 1} (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring))) :=
    inferInstanceAs (HasDerivedCategory.{u + 1}
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
  let dX : HasDerivedCategory.{u + 1} (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring))) :=
    inferInstanceAs (HasDerivedCategory.{u + 1}
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
  let := sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let := sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  have hp := presentation_unit (dC := dY) (dE := dX)
    (dD := inferInstanceAs (HasDerivedCategory.{u + 2}
      (proEtaleRingModules Y (proEtaleConstantRing Y P.Ring))))
    (dF := inferInstanceAs (HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X P.Ring))))
    (sfIntrinsicModuleEquivalence Y P.Ring)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring)) f)
    (sfIntrinsicModuleEquivalence X P.Ring).functor K
  have hn : (P.finiteReductionPullbackPresentation f).choose =
      P.finiteReductionPullbackPresentationNative f :=
    eq_of_heq (P.finiteReductionPullbackPresentation f).choose_spec.1
  simp only [finiteReductionRawPullbackModel, hn, Iso.trans_hom, NatTrans.comp_app,
    rawRealizationSquare, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [Category.assoc]
  congr 1

attribute [local implicit_reducible] finiteReduction ProEtale.scalarExtensionFunctor
private theorem finiteTensorPullbackComparison_realize (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteReduction m hm hmn X).map ((rawRealizationSquare P.Ring f).hom.app K) ≫
      (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
        (P.finiteReductionRingHom m hm hmn) X).hom.app ((P.smoothPurityPullback f).obj K) ≫
      (sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring).functor.map
        (P.finiteTensorPullbackComparison m hm hmn f K).hom =
    (ProEtale.tensorPullbackIso (P.finiteReductionRingHom m hm hmn) f).inv.app
        ((sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj K) ≫
      (proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring f).map
        ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
          (P.finiteReductionRingHom m hm hmn) Y).hom.app K) ≫
      (rawRealizationSquare (P.finiteReductionSetting m hm).Ring f).hom.app
        ((P.finiteTensorReduction m hm hmn Y).obj K) := by
  dsimp (config := { instances := true }) only [Coefficient, coefficientCommRing] at K ⊢
  rw [← rawRealizationSquare_model P f K]
  delta finiteTensorPullbackComparison
  dsimp (config := { instances := true }) only [Coefficient, coefficientCommRing]
  simp only [Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  simp only [← (P.finiteReduction m hm hmn X).map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  delta finiteReductionPullbackComparison
  dsimp (config := { instances := true }) only [Coefficient, coefficientCommRing]
  simp only [Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  simp only [← (P.finiteReduction m hm hmn X).map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  erw [← reassoc_of% (((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel
    f).hom.naturality ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) Y).hom.app K))]
  erw [rawRealizationSquare_model (P.finiteReductionSetting m hm) f
    ((P.finiteTensorReduction m hm hmn Y).obj K)]
  rfl


/-- The recorded coefficient pullback mate respects the exact pullback compositor.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2; expanded parent proof Step 7;
Stacks 07A4 (blueprint: lem-pur-finite-tensor-pullback-composition-reduction).
Proof: the existing scalar-pullback mate calculation gives composition in intrinsic
coordinates. Transpose the ordinary pullback models through the adjunction and
compare their units on sections; naturality and fibre-product restriction identify
their compositors. Exact localization preserves this identity. For the fixed
realization squares, the derived equivalence unit cancels the localization of the
ordinary realization square by its triangle identity. Expanding the recorded
coefficient comparison then gives exactly the scalar mate between these squares.
Paste the three scalar squares with the two pullback compositors and use
faithfulness of realization. No flatness of the quotient ring is used. Identity
maps, empty schemes and equal coefficient levels satisfy the same equations. -/
theorem finiteTensorPullbackCompositionReduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ K,
      (P.finiteTensorReduction m hm hmn X).map
          ((compositionFixedPullbackComp P.Ring f g).hom.app K) ≫
        (P.finiteTensorPullbackComparison m hm hmn f ((P.smoothPurityPullback g).obj K)).hom ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          (P.finiteTensorPullbackComparison m hm hmn g K).hom =
      (P.finiteTensorPullbackComparison m hm hmn (f ≫ g) K).hom ≫
        (compositionFixedPullbackComp (P.finiteReductionSetting m hm).Ring f g).hom.app
          ((P.finiteTensorReduction m hm hmn Z).obj K) := by
  intro K
  exact scalar_coordinates_comp
    (sfIntrinsicDerivedEquivalence Z P.Ring).functor
    (sfIntrinsicDerivedEquivalence Y P.Ring).functor
    (sfIntrinsicDerivedEquivalence X P.Ring).functor
    (sfIntrinsicDerivedEquivalence Z (P.finiteReductionSetting m hm).Ring).functor
    (sfIntrinsicDerivedEquivalence Y (P.finiteReductionSetting m hm).Ring).functor
    (sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring).functor
    (P.smoothPurityPullback g) (P.smoothPurityPullback f) (P.smoothPurityPullback (f ≫ g))
    (proEtaleConstantRingDerivedPullback P.Ring g)
    (proEtaleConstantRingDerivedPullback P.Ring f)
    (proEtaleConstantRingDerivedPullback P.Ring (f ≫ g))
    ((P.finiteReductionSetting m hm).smoothPurityPullback g)
    ((P.finiteReductionSetting m hm).smoothPurityPullback f)
    ((P.finiteReductionSetting m hm).smoothPurityPullback (f ≫ g))
    (proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring g)
    (proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring f)
    (proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring (f ≫ g))
    (P.finiteTensorReduction m hm hmn Z) (P.finiteTensorReduction m hm hmn Y)
    (P.finiteTensorReduction m hm hmn X)
    (P.finiteReduction m hm hmn Z) (P.finiteReduction m hm hmn Y)
    (P.finiteReduction m hm hmn X)
    (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) Z)
    (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) Y)
    (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) X)
    (rawRealizationSquare P.Ring g) (rawRealizationSquare P.Ring f)
    (rawRealizationSquare P.Ring (f ≫ g))
    (rawRealizationSquare (P.finiteReductionSetting m hm).Ring g)
    (rawRealizationSquare (P.finiteReductionSetting m hm).Ring f)
    (rawRealizationSquare (P.finiteReductionSetting m hm).Ring (f ≫ g))
    (ProEtale.tensorPullbackIso (P.finiteReductionRingHom m hm hmn) g).symm
    (ProEtale.tensorPullbackIso (P.finiteReductionRingHom m hm hmn) f).symm
    (ProEtale.tensorPullbackIso (P.finiteReductionRingHom m hm hmn) (f ≫ g)).symm
    (compositionFixedPullbackComp P.Ring f g)
    (compositionFixedPullbackComp (P.finiteReductionSetting m hm).Ring f g)
    (proEtaleConstantRingPullbackComposition f g P.Ring).symm
    (proEtaleConstantRingPullbackComposition f g (P.finiteReductionSetting m hm).Ring).symm
    (P.finiteTensorPullbackComparison m hm hmn g)
    (P.finiteTensorPullbackComparison m hm hmn f)
    (P.finiteTensorPullbackComparison m hm hmn (f ≫ g))
    (rawRealizationSquare_comp P.Ring f g)
    (rawRealizationSquare_comp (P.finiteReductionSetting m hm).Ring f g)
    (scalar_pullback_comp (P.finiteReductionRingHom m hm hmn) f g)
    (finiteTensorPullbackComparison_realize P m hm hmn g)
    (finiteTensorPullbackComparison_realize P m hm hmn f)
    (finiteTensorPullbackComparison_realize P m hm hmn (f ≫ g)) K

end WeilConjectures.PurityFiniteSetting
