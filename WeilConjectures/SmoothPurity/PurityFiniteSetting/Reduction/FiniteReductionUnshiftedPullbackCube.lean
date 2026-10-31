/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantScalarPullbackCube

/-! # Ordinary finite-reduction pullback coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private def conjugate
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {F F' : C ⥤ C'} {G G' : D ⥤ D'} (Q : C ⥤ D) (R : C' ⥤ D')
    (a : F ≅ F') (b : G ≅ G') (e : F ⋙ R ≅ Q ⋙ G) : F' ⋙ R ≅ Q ⋙ G' :=
  Functor.isoWhiskerRight a.symm R ≪≫ e ≪≫ Functor.isoWhiskerLeft Q b
private def paste
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {F : C₀ ⥤ C₁} {H : C₁ ⥤ C₂} {G : D₀ ⥤ D₁} {I : D₁ ⥤ D₂}
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂}
    (e : F ⋙ Q₁ ≅ Q₀ ⋙ G) (h : H ⋙ Q₂ ≅ Q₁ ⋙ I) :
    (F ⋙ H) ⋙ Q₂ ≅ Q₀ ⋙ G ⋙ I :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F h ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e I ≪≫
      Functor.associator _ _ _
private theorem cube_components
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {F : C₀ ⥤ C₁} {U : C₁ ⥤ C₃} {V : C₀ ⥤ C₂} {H : C₂ ⥤ C₃}
    {G : D₀ ⥤ D₁} {I : D₁ ⥤ D₃} {J : D₀ ⥤ D₂} {L : D₂ ⥤ D₃}
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {Q₃ : C₃ ⥤ D₃}
    {eF : F ⋙ Q₁ ≅ Q₀ ⋙ G} {eU : U ⋙ Q₃ ≅ Q₁ ⋙ I}
    {eV : V ⋙ Q₂ ≅ Q₀ ⋙ J} {eH : H ⋙ Q₃ ≅ Q₂ ⋙ L}
    {s : F ⋙ U ≅ V ⋙ H} {t : G ⋙ I ≅ J ⋙ L}
    (hc : Functor.isoWhiskerRight s Q₃ ≪≫ paste eV eH =
      paste eF eU ≪≫ Functor.isoWhiskerLeft Q₀ t) (K : C₀) :
    Q₃.map (s.hom.app K) ≫ eH.hom.app (V.obj K) ≫ L.map (eV.hom.app K) =
      eU.hom.app (F.obj K) ≫ I.map (eF.hom.app K) ≫ t.hom.app (Q₀.obj K) := by
  have h := congr_app (congrArg Iso.hom hc) K
  simpa only [paste, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using h

private def modelPaste
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F F' : C₀ ⥤ C₁} {H H' : C₁ ⥤ C₂} (a : F ≅ F') (b : H ≅ H') :
    F ⋙ H ≅ F' ⋙ H' :=
  Functor.isoWhiskerLeft F b ≪≫ Functor.isoWhiskerRight a H'

private theorem conjugate_paste
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {F F' : C₀ ⥤ C₁} {H H' : C₁ ⥤ C₂}
    {G G' : D₀ ⥤ D₁} {I I' : D₁ ⥤ D₂}
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (a : F ≅ F') (b : H ≅ H') (c : G ≅ G') (d : I ≅ I')
    (e : F ⋙ Q₁ ≅ Q₀ ⋙ G) (h : H ⋙ Q₂ ≅ Q₁ ⋙ I) :
    paste (conjugate Q₀ Q₁ a c e) (conjugate Q₁ Q₂ b d h) =
      conjugate Q₀ Q₂ (modelPaste a b) (modelPaste c d) (paste e h) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [paste, conjugate, modelPaste, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  rw [← d.hom.naturality_assoc, ← d.hom.naturality_assoc]
  have hn := h.hom.naturality (a.inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  have ha := b.inv.naturality (a.inv.app K)
  rw [← Q₂.map_comp_assoc, ← ha]
  simp only [Q₂.map_comp, Category.assoc]
  rfl

private theorem conjugate_square
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {F F' H H' : C ⥤ C'} {G G' I I' : D ⥤ D'}
    (Q : C ⥤ D) (R : C' ⥤ D')
    (a : F ≅ F') (b : H ≅ H') (c : G ≅ G') (d : I ≅ I')
    (e : F ⋙ R ≅ Q ⋙ G) (h : H ⋙ R ≅ Q ⋙ I)
    (s : F ≅ H) (t : G ≅ I)
    (hs : Functor.isoWhiskerRight s R ≪≫ h = e ≪≫ Functor.isoWhiskerLeft Q t) :
    Functor.isoWhiskerRight (a.symm ≪≫ s ≪≫ b) R ≪≫ conjugate Q R b d h =
      conjugate Q R a c e ≪≫ Functor.isoWhiskerLeft Q (c.symm ≪≫ t ≪≫ d) := by
  apply Iso.ext
  ext K
  have hh := congr_app (congrArg Iso.hom hs) K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hh
  simp only [conjugate, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (b.hom.app K) (b.inv.app K), Iso.hom_inv_id_app]
  simp only [R.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hh]

-- Project an object-isomorphism equality while the isomorphism is still abstract.
private theorem square_models {I : Type*} {C : Type*} [Category C]
    (F G : I → C) (e : ∀ i, F i ≅ G i)
    {i j : I} (w : i = j) {A₀ A₁ B₀ B₁ : C}
    (r₀ : A₀ ≅ F i) (r₁ : A₁ ≅ F j)
    (c₀ : G i ≅ B₀) (c₁ : G j ≅ B₁)
    (m₀ : A₀ ≅ B₀) (m₁ : A₁ ≅ B₁)
    (h₀ : r₀ ≪≫ e i ≪≫ c₀ = m₀) (h₁ : r₁ ≪≫ e j ≪≫ c₁ = m₁) :
    m₀.symm ≪≫ r₀ ≪≫ eqToIso (congrArg F w) ≪≫ r₁.symm ≪≫ m₁ =
      c₀.symm ≪≫ eqToIso (congrArg G w) ≪≫ c₁ := by
  cases w
  rw [← h₀, ← h₁]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    eqToIso_refl, Iso.refl_hom, Category.assoc, Category.id_comp,
    Iso.inv_hom_id_assoc]


private theorem conjugate_cube_components
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {F F' : C₀ ⥤ C₁} {U U' : C₁ ⥤ C₃}
    {V V' : C₀ ⥤ C₂} {H H' : C₂ ⥤ C₃}
    {G G' : D₀ ⥤ D₁} {I I' : D₁ ⥤ D₃}
    {J J' : D₀ ⥤ D₂} {L L' : D₂ ⥤ D₃}
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (Q₃ : C₃ ⥤ D₃)
    (aF : F ≅ F') (aU : U ≅ U') (aV : V ≅ V') (aH : H ≅ H')
    (bF : G ≅ G') (bU : I ≅ I') (bV : J ≅ J') (bH : L ≅ L')
    (eF : F ⋙ Q₁ ≅ Q₀ ⋙ G) (eU : U ⋙ Q₃ ≅ Q₁ ⋙ I)
    (eV : V ⋙ Q₂ ≅ Q₀ ⋙ J) (eH : H ⋙ Q₃ ≅ Q₂ ⋙ L)
    (s : F ⋙ U ≅ V ⋙ H) (t : G ⋙ I ≅ J ⋙ L)
    (hc : Functor.isoWhiskerRight s Q₃ ≪≫ paste eV eH =
      paste eF eU ≪≫ Functor.isoWhiskerLeft Q₀ t) (K : C₀) :
    Q₃.map (((modelPaste aF aU).symm ≪≫ s ≪≫ modelPaste aV aH).hom.app K) ≫
      (conjugate Q₂ Q₃ aH bH eH).hom.app (V'.obj K) ≫
      L'.map ((conjugate Q₀ Q₂ aV bV eV).hom.app K) =
    (conjugate Q₁ Q₃ aU bU eU).hom.app (F'.obj K) ≫
      I'.map ((conjugate Q₀ Q₁ aF bF eF).hom.app K) ≫
      ((modelPaste bF bU).symm ≪≫ t ≪≫ modelPaste bV bH).hom.app (Q₀.obj K) := by
  refine cube_components
    (eF := conjugate Q₀ Q₁ aF bF eF) (eU := conjugate Q₁ Q₃ aU bU eU)
    (eV := conjugate Q₀ Q₂ aV bV eV) (eH := conjugate Q₂ Q₃ aH bH eH)
    (s := (modelPaste aF aU).symm ≪≫ s ≪≫ modelPaste aV aH)
    (t := (modelPaste bF bU).symm ≪≫ t ≪≫ modelPaste bV bH) ?_ K
  rw [conjugate_paste, conjugate_paste]
  exact conjugate_square Q₀ Q₃ (modelPaste aF aU) (modelPaste aV aH)
    (modelPaste bF bU) (modelPaste bV bH) (paste eF eU) (paste eV eH) s t hc

private theorem conjugate_cube_isos
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {F F' : C₀ ⥤ C₁} {U U' : C₁ ⥤ C₃}
    {V V' : C₀ ⥤ C₂} {H H' : C₂ ⥤ C₃}
    {G G' : D₀ ⥤ D₁} {I I' : D₁ ⥤ D₃}
    {J J' : D₀ ⥤ D₂} {L L' : D₂ ⥤ D₃}
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (Q₃ : C₃ ⥤ D₃)
    (aF : F ≅ F') (aU : U ≅ U') (aV : V ≅ V') (aH : H ≅ H')
    (bF : G ≅ G') (bU : I ≅ I') (bV : J ≅ J') (bH : L ≅ L')
    (eF : F ⋙ Q₁ ≅ Q₀ ⋙ G) (eU : U ⋙ Q₃ ≅ Q₁ ⋙ I)
    (eV : V ⋙ Q₂ ≅ Q₀ ⋙ J) (eH : H ⋙ Q₃ ≅ Q₂ ⋙ L)
    (s : F ⋙ U ≅ V ⋙ H) (t : G ⋙ I ≅ J ⋙ L)
    (hc : Functor.isoWhiskerRight s Q₃ ≪≫ paste eV eH =
      paste eF eU ≪≫ Functor.isoWhiskerLeft Q₀ t) (K : C₀) :
    Q₃.mapIso (((modelPaste aF aU).symm ≪≫ s ≪≫ modelPaste aV aH).app K) ≪≫
      (conjugate Q₂ Q₃ aH bH eH).app (V'.obj K) ≪≫
      L'.mapIso ((conjugate Q₀ Q₂ aV bV eV).app K) =
    (conjugate Q₁ Q₃ aU bU eU).app (F'.obj K) ≪≫
      I'.mapIso ((conjugate Q₀ Q₁ aF bF eF).app K) ≪≫
      ((modelPaste bF bU).symm ≪≫ t ≪≫ modelPaste bV bH).app (Q₀.obj K) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
    conjugate_cube_components Q₀ Q₁ Q₂ Q₃ aF aU aV aH bF bU bV bH
      eF eU eV eH s t hc K

private theorem iso_cube_finish
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (R : C ⥤ D) (I : F ⥤ D) (L : E ⥤ D)
    {A B : C} {P Q : E} {U V : F}
    (s s' : A ≅ B) (a : R.obj B ≅ L.obj P) (b : P ≅ Q)
    (d : R.obj A ≅ I.obj U) (e : U ≅ V) (t t' : I.obj V ≅ L.obj Q)
    (h : R.mapIso s ≪≫ a ≪≫ L.mapIso b = d ≪≫ I.mapIso e ≪≫ t)
    (hs : s = s') (ht : t = t') :
    R.map s'.hom ≫ a.hom ≫ L.map b.hom = d.hom ≫ I.map e.hom ≫ t'.hom := by
  cases hs
  cases ht
  simpa only [Iso.trans_hom, Functor.mapIso_hom] using congrArg Iso.hom h

private theorem compositor_model {C : Type*} [Category C]
    {A B D E : C} (r : A ≅ B) (e : B ≅ D) (c : D ≅ E) (m : A ≅ E)
    (h : e ≪≫ c = r.symm ≪≫ m) : r ≪≫ e ≪≫ c = m := by
  apply Iso.ext
  have hh := congrArg (fun z ↦ r.hom ≫ z.hom) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc] using hh

private theorem derive_compositor
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F G : C ⥤ D) (F' G' : D ⥤ E) (Fc Gc : C ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [Fc.Additive] [Gc.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits Fc] [PreservesFiniteColimits Fc]
    [PreservesFiniteLimits Gc] [PreservesFiniteColimits Gc]
    (q : F ≅ G) (q' : F' ≅ G') (qc : Fc ≅ Gc)
    (cF : Fc ≅ F ⋙ F') (cG : Gc ≅ G ⋙ G')
    (h : qc ≪≫ cG = cF ≪≫ Functor.isoWhiskerLeft F q' ≪≫
      Functor.isoWhiskerRight q G') :
    Functor.mapDerivedCategoryNatIso qc ≪≫
        (Functor.mapDerivedCategoryNatIso cG ≪≫ Functor.mapDerivedCategoryCompIso G G') =
      (Functor.mapDerivedCategoryNatIso cF ≪≫ Functor.mapDerivedCategoryCompIso F F') ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso q') ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso q) G'.mapDerivedCategory := by
  apply Iso.ext
  have hh := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom ≫
    (Functor.mapDerivedCategoryCompIso G G').hom) h
  simp only [Functor.mapDerivedCategoryNatIso_trans, Iso.trans_hom, Category.assoc] at hh ⊢
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerRight q G',
    reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F q')] at hh
  exact hh

open AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
private theorem ordinary_model_composition (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ Z) :
    ∃ a : proEtaleConstantRingPullback A (h ≫ f) ≅
        proEtaleConstantRingPullback A f ⋙ proEtaleConstantRingPullback A h,
      Functor.mapDerivedCategoryNatIso a ≪≫
          Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A f)
            (proEtaleConstantRingPullback A h) =
        (proEtaleConstantRingPullbackComposition h f A).symm ∧
      openSquarePullbackModel A (h ≫ f) ≪≫ sfIntrinsicPullbackComp A h f =
        a ≪≫ Functor.isoWhiskerLeft (proEtaleConstantRingPullback A f)
          (openSquarePullbackModel A h) ≪≫
        Functor.isoWhiskerRight (openSquarePullbackModel A f) (sfIntrinsicPullback A h) := by
  obtain ⟨a, ha, hd⟩ := proEtaleConstantRingPullbackComposition_ordinary h f A
  refine ⟨a, hd, ?_⟩
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((proEtaleConstantRingAdjunction A (h ≫ f)).homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext z
  let v := (openSquarePullbackModel A h).hom.app
      ((proEtaleConstantRingPullback A f).obj M) ≫
    (sfIntrinsicPullback A h).map ((openSquarePullbackModel A f).hom.app M)
  change ((sfIntrinsicPullbackComp A h f).hom.app M).val.app _
    (((openSquarePullbackModel A (h ≫ f)).hom.app M).val.app _
      (((proEtaleConstantRingAdjunction A (h ≫ f)).unit.app M).val.app V z)) =
    v.val.app _ ((a.hom.app M).val.app _
      (((proEtaleConstantRingAdjunction A (h ≫ f)).unit.app M).val.app V z))
  erw [(openSquarePullbackModel_existsUnique A (h ≫ f)).exists.choose_spec M V.unop z]
  erw [finiteIntrinsicPullback_unit_comp A f h M V.unop z, ha M V.unop z]
  erw [PresheafOfModules.naturality_apply]
  congr 1
  change _ = ((sfIntrinsicPullback A h).map
    ((openSquarePullbackModel A f).hom.app M)).val.app _
      (((openSquarePullbackModel A h).hom.app _).val.app _ _)
  erw [(openSquarePullbackModel_existsUnique A h).exists.choose_spec]
  have hn := congrArg (fun t ↦ t.val.app (op ((proEtaleBaseChange f).obj V.unop))
      (((proEtaleConstantRingAdjunction A f).unit.app M).val.app V z))
    ((sfIntrinsicConstantModuleAdjunction h A).unit.naturality
      ((openSquarePullbackModel A f).hom.app M))
  change ((sfIntrinsicConstantModuleAdjunction h A).unit.app _).val.app _
      (((openSquarePullbackModel A f).hom.app M).val.app _ _) =
    ((sfIntrinsicPullback A h).map ((openSquarePullbackModel A f).hom.app M)).val.app _ _ at hn
  have hu := (openSquarePullbackModel_existsUnique A f).exists.choose_spec M V.unop z
  have hh := congrArg (fun w ↦
    (((sfIntrinsicConstantModuleAdjunction h A).unit.app
      ((sfIntrinsicPullback A f).obj M)).val.app
        (op ((proEtaleBaseChange f).obj V.unop))) w) hu
  exact hh.symm.trans hn
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
attribute [local irreducible] sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
private theorem raw_intrinsic_compositor (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ Z) :
    openSquareDerivedPullbackModel A (h ≫ f) ≪≫ sfIntrinsicDerivedPullbackComp A h f =
      (proEtaleConstantRingPullbackComposition h f A).symm ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingDerivedPullback A f)
          (openSquareDerivedPullbackModel A h) ≪≫
        Functor.isoWhiskerRight (openSquareDerivedPullbackModel A f)
          (sfIntrinsicDerivedPullback A h) := by
  obtain ⟨a, ha, hm⟩ := ordinary_model_composition A h f
  have hd := derive_compositor
    (proEtaleConstantRingPullback A f) (sfIntrinsicPullback A f)
    (proEtaleConstantRingPullback A h) (sfIntrinsicPullback A h)
    (proEtaleConstantRingPullback A (h ≫ f)) (sfIntrinsicPullback A (h ≫ f))
    (openSquarePullbackModel A f) (openSquarePullbackModel A h)
    (openSquarePullbackModel A (h ≫ f)) a (sfIntrinsicPullbackComp A h f) hm
  rw [ha] at hd
  exact hd
end AlgebraicGeometry.Scheme


attribute [local irreducible] Functor.mapDerivedCategory
-- Expose only the equivalence projections needed in the endpoint types below.
attribute [local implicit_reducible] CategoryTheory.Equivalence.mapDerivedCategory
  CategoryTheory.Equivalence.mk
private lemma derived_functor
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    e.mapDerivedCategory.functor = e.functor.mapDerivedCategory := rfl
private lemma derived_inverse
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    e.mapDerivedCategory.inverse = e.inverse.mapDerivedCategory := rfl

private lemma derived_inverse_triangle
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (Y : DerivedCategory C) :
    e.functor.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso e.functor e.inverse).inv.app Y) ≫
          (Functor.mapDerivedCategoryNatIso e.unitIso.symm).hom.app Y ≫
          (Functor.mapDerivedCategoryIdIso C).hom.app Y) =
      (Functor.mapDerivedCategoryCompIso e.inverse e.functor).inv.app
          (e.functor.mapDerivedCategory.obj Y) ≫
        (Functor.mapDerivedCategoryNatIso e.counitIso).hom.app
          (e.functor.mapDerivedCategory.obj Y) ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app (e.functor.mapDerivedCategory.obj Y) := by
  have h := Functor.mapDerivedCategoryCompNatIso_cocycle
    e.unitIso.symm (Iso.refl e.functor) e.counitIso (Iso.refl e.functor)
    (fun X ↦ by simpa using (e.counit_app_functor X).symm) Y
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom] at h
  have hl := congr_app (Functor.mapDerivedCategoryCompIso_id_comp e.functor) Y
  have hr := congr_app (Functor.mapDerivedCategoryCompIso_comp_id e.functor) Y
  simp only [NatTrans.comp_app, NatTrans.id_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hl hr
  have hl' : (Functor.mapDerivedCategoryCompIso (𝟭 C) e.functor).inv.app Y =
      e.functor.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).hom.app Y) := by
    exact ((Iso.hom_comp_eq_id
      ((Functor.mapDerivedCategoryCompIso (𝟭 C) e.functor).app Y)).mp hl).symm
  have hr' : (Functor.mapDerivedCategoryCompIso e.functor (𝟭 D)).inv.app Y =
      (Functor.mapDerivedCategoryIdIso D).hom.app
        (e.functor.mapDerivedCategory.obj Y) := by
    exact ((Iso.hom_comp_eq_id
      ((Functor.mapDerivedCategoryCompIso e.functor (𝟭 D)).app Y)).mp hr).symm
  rw [hl', hr'] at h
  apply (cancel_mono ((Functor.mapDerivedCategoryNatIso (Iso.refl e.functor)).hom.app Y)).mp
  simpa only [Functor.map_comp, Category.assoc] using h


private lemma derived_unit_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (Y : DerivedCategory C) :
    e.mapDerivedCategory.unitIso.inv.app Y =
      (Functor.mapDerivedCategoryCompIso e.functor e.inverse).inv.app Y ≫
        (Functor.mapDerivedCategoryNatIso e.unitIso.symm).hom.app Y ≫
        (Functor.mapDerivedCategoryIdIso C).hom.app Y := by
  apply e.mapDerivedCategory.functor.map_injective
  rw [← e.mapDerivedCategory.counit_app_functor]
  exact (derived_inverse_triangle e Y).symm

private lemma derived_unit_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] :
    e.mapDerivedCategory.unitIso =
      (Functor.mapDerivedCategoryIdIso C).symm ≪≫
        Functor.mapDerivedCategoryNatIso e.unitIso ≪≫
        Functor.mapDerivedCategoryCompIso e.functor e.inverse := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  ext Y
  simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc] using derived_unit_inv e Y

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private lemma derive_insertUnit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (G : C ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (Functor.mapDerivedCategoryNatIso (e.funInvIdAssoc G).symm).hom ≫
        (Functor.mapDerivedCategoryCompIso e.functor (e.inverse ⋙ G)).hom ≫
        Functor.whiskerLeft e.functor.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso e.inverse G).hom =
      Functor.whiskerRight e.mapDerivedCategory.unitIso.hom G.mapDerivedCategory := by
  have he : (e.funInvIdAssoc G).symm = Functor.isoWhiskerRight e.unitIso G := by
    apply Iso.ext
    ext X
    simp only [Iso.symm_hom, Equivalence.funInvIdAssoc_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [he, Functor.mapDerivedCategoryCompIso_assoc,
    ← Category.assoc, Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  ext Y
  have hid := congr_app (Functor.mapDerivedCategoryCompIso_id_comp G) Y
  have hid' : (Functor.mapDerivedCategoryCompIso (𝟭 C) G).hom.app Y =
      G.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).inv.app Y) := by
    apply (cancel_mono
      (G.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).hom.app Y))).mp
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app,
      ← G.mapDerivedCategory.map_comp, Iso.inv_hom_id_app, G.mapDerivedCategory.map_id,
      Functor.comp_obj, Functor.id_obj] using hid
  simp only [derived_unit_iso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, G.mapDerivedCategory.map_comp, Category.assoc, hid']

section
variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
  [Abelian C] [Abelian D] [Abelian E] [Abelian H]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory H]
  (F : C ⥤ D) (G : D ⥤ E) (J : E ⥤ H)
  [F.Additive] [G.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
@[reassoc] private lemma derive_assoc_app (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompIso F (G ⋙ J)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso G J).hom.app (F.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategoryCompIso (F ⋙ G) J).hom.app K ≫
        J.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F G).hom.app K) := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using
    congr_app (Functor.mapDerivedCategoryCompIso_assoc F G J) K
end
section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  {F F' : C ⥤ D} {G G' : D ⥤ E}
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
@[reassoc] private lemma derive_whiskerLeft_app (e : G ≅ G') (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F e)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso F G').hom.app K =
      (Functor.mapDerivedCategoryCompIso F G).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso e).hom.app (F.mapDerivedCategory.obj K) := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
    congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
@[reassoc] private lemma derive_whiskerRight_app (e : F ≅ F') (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e G)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso F' G).hom.app K =
      (Functor.mapDerivedCategoryCompIso F G).hom.app K ≫
        G.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso e).hom.app K) := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using
    congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e G) K
end

attribute [local irreducible] Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso
private lemma derive_insert_paste
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [Abelian C] [Abelian D] [Abelian E] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory H]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e : D ≌ E) [e.functor.Additive] [e.inverse.Additive]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso
      (Functor.isoWhiskerLeft P (e.funInvIdAssoc G).symm)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso (P ⋙ e.functor) (e.inverse ⋙ G)).hom.app K ≫
        (e.inverse ⋙ G).mapDerivedCategory.map
          ((Functor.mapDerivedCategoryCompIso P e.functor).hom.app K) ≫
        (Functor.mapDerivedCategoryCompIso e.inverse G).hom.app
          (e.functor.mapDerivedCategory.obj (P.mapDerivedCategory.obj K)) =
      (Functor.mapDerivedCategoryCompIso P G).hom.app K ≫
        G.mapDerivedCategory.map (e.mapDerivedCategory.unitIso.hom.app
          (P.mapDerivedCategory.obj K)) := by
  have hn := (Functor.mapDerivedCategoryCompIso e.inverse G).hom.naturality
    ((Functor.mapDerivedCategoryCompIso P e.functor).hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn, derive_assoc_app_assoc (P ⋙ e.functor) e.inverse G]
  rw [← G.mapDerivedCategory.map_comp, ← derive_assoc_app P e.functor e.inverse]
  simp only [G.mapDerivedCategory.map_comp]
  erw [← derive_assoc_app_assoc P (e.functor ⋙ e.inverse) G,
    ← derive_assoc_app e.functor e.inverse G]
  erw [derive_whiskerLeft_app_assoc (F := P) (e.funInvIdAssoc G).symm]
  have hi := congr_app (derive_insertUnit e G) (P.mapDerivedCategory.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hi
  rw [hi]

section
variable {S C D E T J : Type*}
  [Category S] [Category C] [Category D] [Category E] [Category T] [Category J]
  [Abelian S] [Abelian C] [Abelian D] [Abelian E] [Abelian T] [Abelian J]
  [HasDerivedCategory S] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory T] [HasDerivedCategory J]
  (A : S ⥤ C) (F : C ⥤ D) (G : D ⥤ E) (B : E ⥤ T) (e : D ≌ J)
  [A.Additive] [F.Additive] [G.Additive] [B.Additive]
  [e.functor.Additive] [e.inverse.Additive]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]
private lemma native_insert (K : DerivedCategory S) :
    (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft A
      (Functor.isoWhiskerLeft F (e.funInvIdAssoc (G ⋙ B)).symm))).hom.app K ≫
      (Functor.mapDerivedCategoryCompIso (A ⋙ F ⋙ e.functor)
        (e.inverse ⋙ G ⋙ B)).hom.app K ≫
      (e.inverse ⋙ G ⋙ B).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso A (F ⋙ e.functor)).hom.app K) ≫
      (e.inverse ⋙ G ⋙ B).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso F e.functor).hom.app
          (A.mapDerivedCategory.obj K)) ≫
      (Functor.mapDerivedCategoryCompIso e.inverse (G ⋙ B)).hom.app
        (e.functor.mapDerivedCategory.obj
          (F.mapDerivedCategory.obj (A.mapDerivedCategory.obj K))) ≫
      (Functor.mapDerivedCategoryCompIso G B).hom.app
        (e.inverse.mapDerivedCategory.obj (e.functor.mapDerivedCategory.obj
          (F.mapDerivedCategory.obj (A.mapDerivedCategory.obj K)))) =
    (Functor.mapDerivedCategoryCompIso (A ⋙ F ⋙ G) B).hom.app K ≫
      B.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso A (F ⋙ G)).hom.app K) ≫
      B.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso F G).hom.app (A.mapDerivedCategory.obj K)) ≫
      B.mapDerivedCategory.map (G.mapDerivedCategory.map
        (e.mapDerivedCategory.unitIso.hom.app
          (F.mapDerivedCategory.obj (A.mapDerivedCategory.obj K)))) := by
  have hi := derive_insert_paste F e (G ⋙ B) (A.mapDerivedCategory.obj K)
  have hn := (Functor.mapDerivedCategoryCompIso G B).hom.naturality
    (e.mapDerivedCategory.unitIso.hom.app
      (F.mapDerivedCategory.obj (A.mapDerivedCategory.obj K)))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    derived_functor, derived_inverse] at hn
  conv_lhs =>
    rw [← derive_assoc_app_assoc]
    erw [derive_whiskerLeft_app_assoc (F := A)
      (Functor.isoWhiskerLeft F (e.funInvIdAssoc (G ⋙ B)).symm)]
  rw [reassoc_of% hi, hn]
  rw [derive_assoc_app_assoc F G B]
  erw [derive_assoc_app_assoc A (F ⋙ G) B]
end

section
variable {S C D E : Type*} [Category S] [Category C] [Category D] [Category E]
  [Abelian S] [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory S] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory E]
  (A : S ⥤ C) (F G : C ⥤ D) (B : D ⥤ E)
  [A.Additive] [F.Additive] [G.Additive] [B.Additive]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]
private lemma native_map (c : F ≅ G) (K : DerivedCategory S) :
    (Functor.mapDerivedCategoryNatIso
      (Functor.isoWhiskerLeft A (Functor.isoWhiskerRight c B))).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso (A ⋙ G) B).hom.app K ≫
        B.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso A G).hom.app K) =
      (Functor.mapDerivedCategoryCompIso (A ⋙ F) B).hom.app K ≫
        B.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso A F).hom.app K) ≫
        B.mapDerivedCategory.map
          ((Functor.mapDerivedCategoryNatIso c).hom.app (A.mapDerivedCategory.obj K)) := by
  rw [← derive_assoc_app, derive_whiskerLeft_app_assoc,
    derive_whiskerRight_app, derive_assoc_app_assoc]
end

namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Scheme.sfIntrinsicTransport Scheme.sfIntrinsicPullback
  Scheme.sfIntrinsicDerivedEquivalence Coefficient coefficientCommRing
  smoothPurityPullback finiteReductionPullback
private lemma native_right (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
    let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
    (P.finiteReductionPullbackPresentationNative f).hom.app K =
      (Functor.mapDerivedCategoryCompIso
        (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).inverse
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f ⋙
          (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor)).hom.app K ≫
      (Functor.mapDerivedCategoryCompIso
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)
        (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor).hom.app
        ((Scheme.sfIntrinsicModuleEquivalence Y P.Ring).inverse.mapDerivedCategory.obj K) := by
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  exact (derive_assoc_app _ _ _ K).symm
private theorem native_compositor (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ Z)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    (P.finiteReductionPullbackPresentationNative (h ≫ f)).hom.app K ≫
        (P.finiteReductionPullbackCompositor h f K).hom =
      (Scheme.sfIntrinsicDerivedPullbackComp P.Ring h f).hom.app K ≫
        (Scheme.sfIntrinsicDerivedPullback P.Ring h).map
          ((P.finiteReductionPullbackPresentationNative f).hom.app K) ≫
        (P.finiteReductionPullbackPresentationNative h).hom.app
          ((P.finiteReductionPullback f).obj K) := by
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Z
  have hc : compositionFixedPullbackComp P.Ring h f =
      compositionPullbackComp (ModuleCat.{u + 1} P.Coefficient) h f :=
    eq_of_heq (existsUnique_compositionFixedPullbackComp P.Ring h f).choose_spec.1
  let A := (Scheme.sfIntrinsicModuleEquivalence Z P.Ring).inverse
  let F := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f
  let G := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h
  let B := (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor
  let e := Scheme.sfIntrinsicModuleEquivalence Y P.Ring
  let c := ProEtale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) h f
  let : (Scheme.sfIntrinsicTransport P.Ring (F ⋙ G)).Additive :=
    inferInstanceAs (A ⋙ F ⋙ G ⋙ B).Additive
  let : PreservesFiniteLimits (Scheme.sfIntrinsicTransport P.Ring (F ⋙ G)) :=
    inferInstanceAs (PreservesFiniteLimits (A ⋙ F ⋙ G ⋙ B))
  let : PreservesFiniteColimits (Scheme.sfIntrinsicTransport P.Ring (F ⋙ G)) :=
    inferInstanceAs (PreservesFiniteColimits (A ⋙ F ⋙ G ⋙ B))
  have hm := native_map A _ (F ⋙ G) B c K
  have hi := native_insert A F G B e K
  have he : Scheme.sfIntrinsicTransportComp P.Ring F G =
      Functor.isoWhiskerLeft A
        (Functor.isoWhiskerLeft F (e.funInvIdAssoc (G ⋙ B)).symm) := by
    apply Iso.ext
    ext M
    simp only [Scheme.sfIntrinsicTransportComp, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Equivalence.funInvIdAssoc_inv_app, Functor.comp_map]
    rfl
  have hm' := congrArg (fun z ↦ z ≫
      B.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F G).hom.app
        (A.mapDerivedCategory.obj K)) ≫
      B.mapDerivedCategory.map (G.mapDerivedCategory.map
        (e.mapDerivedCategory.unitIso.hom.app
          (F.mapDerivedCategory.obj (A.mapDerivedCategory.obj K))))) hm
  have hi' := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso
      (Functor.isoWhiskerLeft A (Functor.isoWhiskerRight c B))).hom.app K ≫ z) hi.symm
  simp only [Category.assoc] at hm' hi'
  have hh := hm'.symm.trans hi'
  rw [native_right P f, native_right P h]
  dsimp only [finiteReductionPullbackPresentationNative, finiteReductionPullbackCompositor]
  rw [hc]
  simp only [Scheme.sfIntrinsicDerivedPullbackComp, Scheme.sfIntrinsicPullbackComp,
    Scheme.sfIntrinsicTransportIso]
  erw [he]
  have ht := Functor.mapDerivedCategoryNatIso_trans
    (Functor.isoWhiskerLeft A (Functor.isoWhiskerRight c B))
    (Functor.isoWhiskerLeft A
      (Functor.isoWhiskerLeft F (e.funInvIdAssoc (G ⋙ B)).symm))
  simp only [Iso.trans_hom, NatTrans.comp_app]
  erw [ht]
  simp only [Scheme.sfIntrinsicDerivedEquivalence, derived_functor, derived_inverse,
    smoothPurityPullback, ProEtale.sfFixedDerivedPullback, finiteReductionPullback,
    Functor.comp_obj, compositionPullbackComp, compositionExactDerivedComp,
    Iso.app_hom, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simpa only [A, F, G, B, e, c, Category.assoc,
    Scheme.sfIntrinsicDerivedPullback, Scheme.sfIntrinsicPullback,
    Scheme.sfIntrinsicTransport, Coefficient, coefficientCommRing,
    derived_unit_iso, derived_functor, derived_inverse, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj, Functor.map_comp] using hh

private theorem rawModel_native (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P.finiteReductionRawPullbackModel f =
      Scheme.openSquareDerivedPullbackModel P.Ring f ≪≫
        P.finiteReductionPullbackPresentationNative f := by
  unfold finiteReductionRawPullbackModel
  rw [eq_of_heq (P.finiteReductionPullbackPresentation f).choose_spec.1]
private theorem raw_model_compositor (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ Z)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    (P.finiteReductionRawPullbackModel (h ≫ f)).app K ≪≫
      P.finiteReductionPullbackCompositor h f K =
    (Scheme.proEtaleConstantRingPullbackComposition h f P.Ring).symm.app K ≪≫
      (modelPaste (P.finiteReductionRawPullbackModel f)
        (P.finiteReductionRawPullbackModel h)).app K := by
  have hn := native_compositor P h f K
  have hr := congr_app (congrArg Iso.hom (Scheme.raw_intrinsic_compositor P.Ring h f)) K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at hr
  apply Iso.ext
  simp only [rawModel_native, modelPaste, Iso.app_hom, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  rw [hn, reassoc_of% hr]
  rw [← (Scheme.sfIntrinsicDerivedPullback P.Ring h).map_comp_assoc]
  have ht := (P.finiteReductionPullbackPresentationNative h).hom.naturality
    ((Scheme.openSquareDerivedPullbackModel P.Ring f).hom.app K ≫
      (P.finiteReductionPullbackPresentationNative f).hom.app K)
  rw [ht]
  simp only [Functor.map_comp, Iso.symm_hom]

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.Scheme
private theorem canonical_comparisons
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ) :
    proEtaleCanonicalPullbackComposition h k RV RW RZ ck ch =
      proEtaleCanonicalDerivedPullbackComparison h k RV RW RZ ck ch := by
  let t := proEtaleCanonicalPullbackComposition_existsUnique h k RV RW RZ ck ch
    (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) rfl
  apply t.unique (Classical.choose_spec t.exists)
  unfold proEtaleCanonicalDerivedPullbackComparison
  extract_lets chk hex
  exact Classical.choose_spec hex
private theorem transportIso_paste {C : Type*} [Category C]
    {P P' Q Q' L R : C} (a : P ≅ L) (b : Q ≅ R)
    (e : P' = P) (e' : Q' = Q) (h : P = Q) (h' : P' = Q') :
    a.symm ≪≫ eqToIso h ≪≫ b =
      (eqToIso e ≪≫ a).symm ≪≫ eqToIso h' ≪≫ (eqToIso e' ≪≫ b) := by
  cases e
  cases e'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  simp only [eqToIso_refl, Iso.refl_trans]


private theorem raw_square_composition
    (A : Type u) [CommRing A] {X' X Y' Y : Scheme.{u}}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare h f' f g) :
    ProEtale.directImageConstantPullbackIso A sq =
      proEtaleConstantRingPullbackComposition f' g A ≪≫
        eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) sq.w.symm) ≪≫
        (proEtaleConstantRingPullbackComposition h f A).symm := by
  let c {V W Z : Scheme.{u}} (a : Z ⟶ W) (b : W ⟶ V) :=
    eqToIso (congrArg
      (proEtaleRingDerivedPullback (a ≫ b) (proEtaleConstantRing V A)
        (proEtaleConstantRing Z A))
      (proEtaleConstantRingCompositeCoefficients_eq a b A).symm) ≪≫
        proEtaleCanonicalDerivedPullbackComparison a b
          (proEtaleConstantRing V A) (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
          (proEtaleConstantRingComparison b A) (proEtaleConstantRingComparison a A)
  have ht : ProEtale.directImageConstantPullbackIso A sq =
      (c f' g).symm ≪≫
        eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) sq.w.symm) ≪≫ c h f := by
    let ep := congrArg
      (proEtaleRingDerivedPullback (f' ≫ g) (proEtaleConstantRing Y A)
        (proEtaleConstantRing X' A))
      (proEtaleConstantRingCompositeCoefficients_eq f' g A).symm
    let eq := congrArg
      (proEtaleRingDerivedPullback (h ≫ f) (proEtaleConstantRing Y A)
        (proEtaleConstantRing X' A))
      (proEtaleConstantRingCompositeCoefficients_eq h f A).symm
    let ew := congrArg (proEtaleConstantRingDerivedPullback A) sq.w.symm
    unfold ProEtale.directImageConstantPullbackIso proEtaleAmbientRingedPullbackComparison
    dsimp only
    exact (Iso.trans_assoc _ _ _).trans (transportIso_paste
      (proEtaleCanonicalDerivedPullbackComparison f' g
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y' A) (proEtaleConstantRing X' A)
        (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison f' A))
      (proEtaleCanonicalDerivedPullbackComparison h f
        (proEtaleConstantRing Y A) (proEtaleConstantRing X A) (proEtaleConstantRing X' A)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison h A))
      ep eq (ep.symm.trans (ew.trans eq)) ew)
  rw [ht]
  dsimp only [c]
  rw [proEtaleConstantRingPullbackComposition_eq,
    proEtaleConstantRingPullbackComposition_eq,
    canonical_comparisons, canonical_comparisons]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme

private theorem raw_cube_generic {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : ChosenCartesianSquare u f' f v) :
    Functor.isoWhiskerRight (ProEtale.directImageConstantPullbackIso A sq).symm
        (ProEtale.directImageScalarExtension φ X') ≪≫
      paste (ProEtale.directImageScalarPullbackIso φ v).symm
        (ProEtale.directImageScalarPullbackIso φ f').symm =
    paste (ProEtale.directImageScalarPullbackIso φ f).symm
        (ProEtale.directImageScalarPullbackIso φ u).symm ≪≫
      Functor.isoWhiskerLeft (ProEtale.directImageScalarExtension φ Y)
        (ProEtale.directImageConstantPullbackIso B sq).symm := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  ext K
  have h := NatTrans.congr_app (Scheme.proEtaleConstantScalarPullback_cube φ sq) K
  simpa only [paste, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc] using h.symm

namespace WeilConjectures.PurityFiniteSetting
private def rawCoefficientIso (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.proEtaleConstantRingDerivedPullback P.Ring f ⋙ P.finiteReduction m hm hmn X ≅
      P.finiteReduction m hm hmn Y ⋙
        Scheme.proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring f :=
  (ProEtale.directImageScalarPullbackIso (P.finiteReductionRingHom m hm hmn) f).symm

private theorem raw_cube (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : ChosenCartesianSquare u f' f v) :
    Functor.isoWhiskerRight (ProEtale.directImageConstantPullbackIso P.Ring sq).symm
        (P.finiteReduction m hm hmn X') ≪≫
      paste (rawCoefficientIso P m hm hmn v) (rawCoefficientIso P m hm hmn f') =
    paste (rawCoefficientIso P m hm hmn f) (rawCoefficientIso P m hm hmn u) ≪≫
      Functor.isoWhiskerLeft (P.finiteReduction m hm hmn Y)
        (ProEtale.directImageConstantPullbackIso (P.finiteReductionSetting m hm).Ring sq).symm := by
  exact raw_cube_generic (P.finiteReductionRingHom m hm hmn) u f' f v sq

attribute [local irreducible] Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Scheme.sfIntrinsicDerivedEquivalence
private def modelSquare (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : ChosenCartesianSquare u f' f v) :
    P.finiteReductionPullback f ⋙ P.finiteReductionPullback u ≅
      P.finiteReductionPullback v ⋙ P.finiteReductionPullback f' :=
  (modelPaste (P.finiteReductionRawPullbackModel f)
    (P.finiteReductionRawPullbackModel u)).symm ≪≫
    (ProEtale.directImageConstantPullbackIso P.Ring sq).symm ≪≫
    modelPaste (P.finiteReductionRawPullbackModel v)
      (P.finiteReductionRawPullbackModel f')
private def comparisonIso (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P.finiteReductionPullback f ⋙ P.finiteReduction m hm hmn X ≅
      P.finiteReduction m hm hmn Y ⋙
        (P.finiteReductionSetting m hm).finiteReductionPullback f :=
  conjugate (P.finiteReduction m hm hmn Y) (P.finiteReduction m hm hmn X)
    (P.finiteReductionRawPullbackModel f)
    ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f)
    (rawCoefficientIso P m hm hmn f)
private theorem comparison_iso_app (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (comparisonIso P m hm hmn f).app K =
      P.finiteReductionPullbackComparison m hm hmn f K := by
  apply Iso.ext
  rfl
private theorem model_components (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (cs : ChosenCartesianSquare u f' f v) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X').mapIso ((modelSquare P u f' f v cs).app K) ≪≫
      (comparisonIso P m hm hmn f').app ((P.finiteReductionPullback v).obj K) ≪≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback f').mapIso
        ((comparisonIso P m hm hmn v).app K) =
    (comparisonIso P m hm hmn u).app ((P.finiteReductionPullback f).obj K) ≪≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).mapIso
        ((comparisonIso P m hm hmn f).app K) ≪≫
      (modelSquare (P.finiteReductionSetting m hm) u f' f v cs).app
        ((P.finiteReduction m hm hmn Y).obj K) := by
  exact conjugate_cube_isos
    (P.finiteReduction m hm hmn Y) (P.finiteReduction m hm hmn X)
    (P.finiteReduction m hm hmn Y') (P.finiteReduction m hm hmn X')
    (P.finiteReductionRawPullbackModel f) (P.finiteReductionRawPullbackModel u)
    (P.finiteReductionRawPullbackModel v) (P.finiteReductionRawPullbackModel f')
    ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f)
    ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel u)
    ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel v)
    ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f')
    (rawCoefficientIso P m hm hmn f) (rawCoefficientIso P m hm hmn u)
    (rawCoefficientIso P m hm hmn v) (rawCoefficientIso P m hm hmn f')
    (ProEtale.directImageConstantPullbackIso P.Ring cs).symm
    (ProEtale.directImageConstantPullbackIso (P.finiteReductionSetting m hm).Ring cs).symm
    (raw_cube P m hm hmn u f' f v cs) K

private theorem coefficient_components (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (cs : ChosenCartesianSquare u f' f v) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X').mapIso ((modelSquare P u f' f v cs).app K) ≪≫
      P.finiteReductionPullbackComparison m hm hmn f'
        ((P.finiteReductionPullback v).obj K) ≪≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback f').mapIso
        (P.finiteReductionPullbackComparison m hm hmn v K) =
    P.finiteReductionPullbackComparison m hm hmn u
        ((P.finiteReductionPullback f).obj K) ≪≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).mapIso
        (P.finiteReductionPullbackComparison m hm hmn f K) ≪≫
      (modelSquare (P.finiteReductionSetting m hm) u f' f v cs).app
        ((P.finiteReduction m hm hmn Y).obj K) := by
  have h := model_components P m hm hmn u f' f v cs K
  simpa only [comparison_iso_app] using h

-- Explicit model arguments keep the realization matching small.
private theorem square_models_specialized (P : PurityFiniteSetting.{u}) {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hc₀ : (Scheme.proEtaleConstantRingPullbackComposition u f P.Ring).app K ≪≫
      (P.finiteReductionRawPullbackModel (u ≫ f)).app K ≪≫
      P.finiteReductionPullbackCompositor u f K =
        (modelPaste (P.finiteReductionRawPullbackModel f)
          (P.finiteReductionRawPullbackModel u)).app K)
    (hc₁ : (Scheme.proEtaleConstantRingPullbackComposition f' v P.Ring).app K ≪≫
      (P.finiteReductionRawPullbackModel (f' ≫ v)).app K ≪≫
      P.finiteReductionPullbackCompositor f' v K =
        (modelPaste (P.finiteReductionRawPullbackModel v)
          (P.finiteReductionRawPullbackModel f')).app K) :
    (modelPaste (P.finiteReductionRawPullbackModel f)
      (P.finiteReductionRawPullbackModel u)).symm.app K ≪≫
      (Scheme.proEtaleConstantRingPullbackComposition u f P.Ring).app K ≪≫
      eqToIso (congrArg (fun h ↦
        (Scheme.proEtaleConstantRingDerivedPullback P.Ring h).obj K) sq.w) ≪≫
      (Scheme.proEtaleConstantRingPullbackComposition f' v P.Ring).symm.app K ≪≫
      (modelPaste (P.finiteReductionRawPullbackModel v)
        (P.finiteReductionRawPullbackModel f')).app K =
      P.finiteReductionPullbackSquare u f' f v sq K := by
  exact square_models
    (fun h ↦ (Scheme.proEtaleConstantRingDerivedPullback P.Ring h).obj K)
    (fun h ↦ (P.finiteReductionPullback h).obj K)
    (fun h ↦ (P.finiteReductionRawPullbackModel h).app K) sq.w
    ((Scheme.proEtaleConstantRingPullbackComposition u f P.Ring).app K)
    ((Scheme.proEtaleConstantRingPullbackComposition f' v P.Ring).app K)
    (P.finiteReductionPullbackCompositor u f K)
    (P.finiteReductionPullbackCompositor f' v K)
    ((modelPaste (P.finiteReductionRawPullbackModel f)
      (P.finiteReductionRawPullbackModel u)).app K)
    ((modelPaste (P.finiteReductionRawPullbackModel v)
      (P.finiteReductionRawPullbackModel f')).app K) hc₀ hc₁

private theorem model_square_eq (P : PurityFiniteSetting.{u}) {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (modelSquare P u f' f v
      { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
        hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }).app K =
      P.finiteReductionPullbackSquare u f' f v sq K := by
  have hc₀ := compositor_model
    ((Scheme.proEtaleConstantRingPullbackComposition u f P.Ring).app K)
    ((P.finiteReductionRawPullbackModel (u ≫ f)).app K)
    (P.finiteReductionPullbackCompositor u f K)
    ((modelPaste (P.finiteReductionRawPullbackModel f)
      (P.finiteReductionRawPullbackModel u)).app K)
    (raw_model_compositor P u f K)
  have hc₁ := compositor_model
    ((Scheme.proEtaleConstantRingPullbackComposition f' v P.Ring).app K)
    ((P.finiteReductionRawPullbackModel (f' ≫ v)).app K)
    (P.finiteReductionPullbackCompositor f' v K)
    ((modelPaste (P.finiteReductionRawPullbackModel v)
      (P.finiteReductionRawPullbackModel f')).app K)
    (raw_model_compositor P f' v K)
  have hs := square_models_specialized P u f' f v sq K hc₀ hc₁
  dsimp only [modelSquare]
  rw [Scheme.raw_square_composition]
  apply Iso.ext
  simpa only [Iso.app_hom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, eqToIso.hom, eqToIso.inv,
    eqToHom_app, Category.assoc] using congrArg Iso.hom hs

/-- The ordinary coefficient/pullback cube, before shifts.
Source: blueprint finite-reduction-of-purity, Steps 2 and 4; Stacks Tags 0D6D and 06YY.
(blueprint: lem-pur-finite-reduction-unshifted-pullback-cube).

Proof: use the section-unit characterization of openSquarePullbackModel to identify
its transport of the raw ordinary pullback compositor with sfIntrinsicPullbackComp.
Both images of a unit section are the two successive pullbacks of that section,
with the base-change pullbackComp restriction. Exact localization preserves this
identity and the derived compositor. The exact-derived composition comparisons
then identify the resulting intrinsic compositor with finiteReductionPullbackCompositor,
including its intermediate realization unit. Apply these identifications to both
sides of the Cartesian square. The raw coefficient cube is
proEtaleConstantScalarPullback_cube for the quotient ring homomorphism. Conjugate
its four coefficient edges by finiteReductionRawPullbackModel, use naturality to
move these model comparisons across adjacent edges, and cancel inverse pairs.
The normalized geometric compositors give precisely the displayed equation.
No flatness, smoothness, or constructibility is used. Identity arrows, repeated
schemes, empty schemes, and zero objects obey the same unit identities. -/
theorem finiteReduction_unshiftedPullbackCube (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X').map
        (P.finiteReductionPullbackSquare u f' f v sq K).hom ≫
      (P.finiteReductionPullbackComparison m hm hmn f'
        ((P.finiteReductionPullback v).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback f').map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.finiteReductionPullback f).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (P.finiteReductionPullbackComparison m hm hmn f K).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullbackSquare u f' f v sq
        ((P.finiteReduction m hm hmn Y).obj K)).hom := by
  let cs : ChosenCartesianSquare u f' f v :=
    { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
      hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }
  exact iso_cube_finish (P.finiteReduction m hm hmn X')
    ((P.finiteReductionSetting m hm).finiteReductionPullback u)
    ((P.finiteReductionSetting m hm).finiteReductionPullback f')
    ((modelSquare P u f' f v cs).app K) (P.finiteReductionPullbackSquare u f' f v sq K)
    (P.finiteReductionPullbackComparison m hm hmn f'
      ((P.finiteReductionPullback v).obj K))
    (P.finiteReductionPullbackComparison m hm hmn v K)
    (P.finiteReductionPullbackComparison m hm hmn u
      ((P.finiteReductionPullback f).obj K))
    (P.finiteReductionPullbackComparison m hm hmn f K)
    ((modelSquare (P.finiteReductionSetting m hm) u f' f v cs).app
      ((P.finiteReduction m hm hmn Y).obj K))
    ((P.finiteReductionSetting m hm).finiteReductionPullbackSquare u f' f v sq
      ((P.finiteReduction m hm hmn Y).obj K))
    (coefficient_components P m hm hmn u f' f v cs K) (model_square_eq P u f' f v sq K)
    (model_square_eq (P.finiteReductionSetting m hm) u f' f v sq
      ((P.finiteReduction m hm hmn Y).obj K))

end WeilConjectures.PurityFiniteSetting
