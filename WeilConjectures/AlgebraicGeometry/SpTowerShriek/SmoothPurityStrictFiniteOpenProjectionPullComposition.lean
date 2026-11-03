/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence

/-! Open mate after the transported open comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private theorem transport_square_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (T : D₀ ⥤ D₂)
    (p : P ≅ e₀.inverse ⋙ F ⋙ e₁.functor)
    (q : Q ≅ e₁.inverse ⋙ G ⋙ e₂.functor)
    (t : T ≅ e₀.inverse ⋙ H ⋙ e₂.functor)
    (a : T ≅ P ⋙ Q) (h : H ≅ F ⋙ G)
    (ha : ∀ N, a.hom.app N ≫ q.hom.app (P.obj N) ≫
        (e₁.inverse ⋙ G ⋙ e₂.functor).map (p.hom.app N) =
      t.hom.app N ≫ e₂.functor.map (h.hom.app (e₀.inverse.obj N)) ≫
        e₂.functor.map (G.map (e₁.unitIso.hom.app (F.obj (e₀.inverse.obj N)))))
    (M : C₀) :
    a.hom.app (e₀.functor.obj M) ≫
        Q.map ((Functor.isoWhiskerLeft e₀.functor p ≪≫
          e₀.funInvIdAssoc (F ⋙ e₁.functor)).hom.app M) ≫
        (Functor.isoWhiskerLeft e₁.functor q ≪≫
          e₁.funInvIdAssoc (G ⋙ e₂.functor)).hom.app (F.obj M) =
      (Functor.isoWhiskerLeft e₀.functor t ≪≫
          e₀.funInvIdAssoc (H ⋙ e₂.functor)).hom.app M ≫
        e₂.functor.map (h.hom.app M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Equivalence.funInvIdAssoc_hom_app, Functor.comp_map,
    Equivalence.unitInv, Category.assoc]
  have hq := q.hom.naturality
    (p.hom.app (e₀.functor.obj M) ≫ e₁.functor.map (F.map (e₀.unitIso.inv.app M)))
  rw [reassoc_of% hq]
  simp only [Functor.map_comp, Category.assoc]
  have hu := e₁.unitIso.inv.naturality (F.map (e₀.unitIso.inv.app M))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hu
  rw [← e₂.functor.map_comp, ← G.map_comp, hu, G.map_comp, e₂.functor.map_comp]
  have hh := ha (e₀.functor.obj M)
  simp only [Functor.comp_map] at hh
  rw [reassoc_of% hh]
  simp only [← e₂.functor.map_comp, ← G.map_comp, Iso.hom_inv_id_app_assoc]
  have hn := h.hom.naturality (e₀.unitIso.inv.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  exact congrArg (fun z ↦ t.hom.app (e₀.functor.obj M) ≫ e₂.functor.map z) hn.symm

private theorem derive_square_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [Abelian D₀] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (T : D₀ ⥤ D₂)
    [E₀.Additive] [E₁.Additive] [E₂.Additive]
    [F.Additive] [G.Additive] [H.Additive] [P.Additive] [Q.Additive] [T.Additive]
    [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
    [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
    [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (p : E₀ ⋙ P ≅ F ⋙ E₁) (q : E₁ ⋙ Q ≅ G ⋙ E₂)
    (t : E₀ ⋙ T ≅ H ⋙ E₂) (a : T ≅ P ⋙ Q) (h : H ≅ F ⋙ G)
    (ha : Functor.whiskerLeft E₀ a.hom ≫
        Functor.whiskerRight p.hom Q ≫ Functor.whiskerLeft F q.hom =
      t.hom ≫ Functor.whiskerRight h.hom E₂) :
    Functor.whiskerLeft E₀.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso P Q).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso p).hom Q.mapDerivedCategory ≫
      Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategorySquareIso q).hom =
    (Functor.mapDerivedCategorySquareIso t).hom ≫
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso h ≪≫ Functor.mapDerivedCategoryCompIso F G).hom
        E₂.mapDerivedCategory := by
  have he : Functor.isoWhiskerLeft E₀ a ≪≫
      Functor.isoWhiskerRight p Q ≪≫ Functor.isoWhiskerLeft F q =
      t ≪≫ Functor.isoWhiskerRight h E₂ := Iso.ext ha
  have hd := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) he
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hd
  apply NatTrans.ext
  funext M
  have h₁ := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft E₀ a) M
  have h₂ := congr_app (Functor.mapDerivedCategoryCompIso_assoc E₀ P Q) M
  have h₃ := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight p Q) M
  have h₄ := congr_app (Functor.mapDerivedCategoryCompIso_assoc F E₁ Q) M
  have h₅ := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F q) M
  have h₆ := congr_app (Functor.mapDerivedCategoryCompIso_assoc F G E₂) M
  have h₇ := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight h E₂) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at h₁ h₂ h₃ h₄ h₅ h₆ h₇
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso E₀ T).hom.app M)).1
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% h₁]
  rw [reassoc_of% h₂]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h₃]
  rw [← reassoc_of% h₄]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% h₅]
  rw [h₆]
  rw [← reassoc_of% h₇]
  have hh := congr_app hd M
  simp only [NatTrans.comp_app] at hh
  rw [reassoc_of% hh]

-- Invert the square before specializing to derived categories of sheaves.

private theorem inverse_square_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (T : D₀ ⥤ D₂)
    (p : E₀ ⋙ P ≅ F ⋙ E₁) (q : E₁ ⋙ Q ≅ G ⋙ E₂)
    (t : E₀ ⋙ T ≅ H ⋙ E₂) (a : T ≅ P ⋙ Q) (h : H ≅ F ⋙ G)
    (ha : Functor.whiskerLeft E₀ a.hom ≫
        Functor.whiskerRight p.hom Q ≫ Functor.whiskerLeft F q.hom =
      t.hom ≫ Functor.whiskerRight h.hom E₂)
    (M : C₀) :
    E₂.map (h.inv.app M) ≫ t.inv.app M =
      q.inv.app (F.obj M) ≫ Q.map (p.inv.app M) ≫ a.inv.app (E₀.obj M) := by
  have he : Functor.isoWhiskerLeft E₀ a ≪≫
        Functor.isoWhiskerRight p Q ≪≫ Functor.isoWhiskerLeft F q =
      t ≪≫ Functor.isoWhiskerRight h E₂ := Iso.ext ha
  have hi := congrArg Iso.inv he
  have hc := congr_app hi M
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using hc.symm

private theorem derived_rebase_square_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (F F' : C₀ ⥤ C₁) (G G' : C₁ ⥤ C₂) (H H' : C₀ ⥤ C₂)
    (e : F' ≅ F) (d : G' ≅ G) (k : H' ≅ H)
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (T : D₀ ⥤ D₂)
    (p : E₀ ⋙ P ≅ F ⋙ E₁) (q : E₁ ⋙ Q ≅ G ⋙ E₂)
    (t : E₀ ⋙ T ≅ H ⋙ E₂) (a : T ≅ P ⋙ Q) (h : H ≅ F ⋙ G)
    (ha : ∀ M, E₂.map (h.inv.app M) ≫ t.inv.app M =
      q.inv.app (F.obj M) ≫ Q.map (p.inv.app M) ≫ a.inv.app (E₀.obj M))
    (M : C₀) :
    E₂.map ((k ≪≫ h ≪≫ Functor.isoWhiskerRight e.symm G ≪≫
        Functor.isoWhiskerLeft F' d.symm).inv.app M) ≫
      (Functor.isoWhiskerRight k E₂ ≪≫ t.symm).hom.app M =
    (Functor.isoWhiskerRight d E₂ ≪≫ q.symm).hom.app (F'.obj M) ≫
      Q.map ((Functor.isoWhiskerRight e E₁ ≪≫ p.symm).hom.app M) ≫
        a.inv.app (E₀.obj M) := by
  have hx := ha M
  have hq := q.inv.naturality (e.hom.app M)
  simp only [Functor.comp_map] at hq
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [hx]
  rw [reassoc_of% hq]


namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor proEtaleRingModulePullback sfIntrinsicModuleEquivalence

private theorem intrinsic_comp_sections
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
    (x : ((proEtaleConstantModuleDirectImage f A ⋙
      proEtaleConstantModuleDirectImage g A).obj M).val.obj (Opposite.op V)) :
    ((conjugateIsoEquiv
      ((sfIntrinsicConstantModuleAdjunction g A).comp
        (sfIntrinsicConstantModuleAdjunction f A))
      (sfIntrinsicConstantModuleAdjunction (f ≫ g) A)
      (sfIntrinsicPullbackComp A f g)).hom.app M).val.app (Opposite.op V) x =
        M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op x := by
  obtain ⟨y, hy⟩ := (sectionRealization_bijective A Z
    ((proEtaleConstantModuleDirectImage g A).obj
      ((proEtaleConstantModuleDirectImage f A).obj M)) (Opposite.op V)).surjective x
  have hm := WeilConjectures.AmbientCompositor.finite_comp_mate A f g M
  have hv := congrArg (fun t ↦ sectionRealization A X M
    (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V)) ((t.hom.app (Opposite.op V)) y)) hm
  change sectionRealization A X M (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
      (((sectionDirectImageIso A (f ≫ g)).hom.app M).hom.app (Opposite.op V)
        (((sfIntrinsicModuleEquivalence Z A).inverse.map
          (((WeilConjectures.AmbientCompositor.finite A).ordinaryC f g).hom.app M)).hom.app
            (Opposite.op V) y)) =
    sectionRealization A X M (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
      (((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map
        ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
        (((sectionDirectImageIso A f).hom.app M).hom.app
          (Opposite.op ((proEtaleBaseChange g).obj V))
          (((sectionDirectImageIso A g).hom.app
            ((proEtaleConstantModuleDirectImage f A).obj M)).hom.app (Opposite.op V) y))) at hv
  erw [sectionDirectImageIso_normalization, sectionRealization_naturality,
    sectionRealization_restrict, sectionDirectImageIso_normalization,
    sectionDirectImageIso_normalization, hy] at hv
  exact hv

private theorem intrinsic_comp_unit
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleRingModules Z (proEtaleConstantRing Z A)) (V : Z.ProEt)
    (x : M.val.obj (Opposite.op V)) :
    ((sfIntrinsicPullbackComp A f g).hom.app M).val.app
        (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
        (((sfIntrinsicConstantModuleAdjunction (f ≫ g) A).unit.app M).val.app
          (Opposite.op V) x) =
      ((sfIntrinsicPullback A f).obj ((sfIntrinsicPullback A g).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
        (((sfIntrinsicConstantModuleAdjunction f A).unit.app
            ((sfIntrinsicPullback A g).obj M)).val.app
          (Opposite.op ((proEtaleBaseChange g).obj V))
          (((sfIntrinsicConstantModuleAdjunction g A).unit.app M).val.app
            (Opposite.op V) x)) := by
  have q := congrArg (fun k ↦ k.val.app (Opposite.op V) x)
    (unit_conjugateEquiv
      ((sfIntrinsicConstantModuleAdjunction g A).comp
        (sfIntrinsicConstantModuleAdjunction f A))
      (sfIntrinsicConstantModuleAdjunction (f ≫ g) A)
      (sfIntrinsicPullbackComp A f g).hom M)
  rw [Adjunction.comp_unit_app] at q
  change
    ((conjugateIsoEquiv
      ((sfIntrinsicConstantModuleAdjunction g A).comp
        (sfIntrinsicConstantModuleAdjunction f A))
      (sfIntrinsicConstantModuleAdjunction (f ≫ g) A)
      (sfIntrinsicPullbackComp A f g)).hom.app
        ((sfIntrinsicPullback A f).obj ((sfIntrinsicPullback A g).obj M))).val.app
      (Opposite.op V)
      (((sfIntrinsicConstantModuleAdjunction f A).unit.app
          ((sfIntrinsicPullback A g).obj M)).val.app
        (Opposite.op ((proEtaleBaseChange g).obj V))
        (((sfIntrinsicConstantModuleAdjunction g A).unit.app M).val.app
          (Opposite.op V) x)) =
    ((sfIntrinsicPullbackComp A f g).hom.app M).val.app
      (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
      (((sfIntrinsicConstantModuleAdjunction (f ≫ g) A).unit.app M).val.app
        (Opposite.op V) x) at q
  exact q.symm.trans (intrinsic_comp_sections A f g _ V _)

private theorem ordinary_model_comp
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : proEtaleConstantRingPullback A (f ≫ g) ≅
      proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f)
    (ha : ∀ (M : proEtaleRingModules Z (proEtaleConstantRing Z A)) (V : Z.ProEt)
      (x : M.val.obj (Opposite.op V)),
      (a.hom.app M).val.app (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
          (((proEtaleConstantRingAdjunction A (f ≫ g)).unit.app M).val.app
            (Opposite.op V) x) =
        ((proEtaleConstantRingPullback A f).obj
          ((proEtaleConstantRingPullback A g).obj M)).val.map
          ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
          (((proEtaleConstantRingAdjunction A f).unit.app
              ((proEtaleConstantRingPullback A g).obj M)).val.app
            (Opposite.op ((proEtaleBaseChange g).obj V))
            (((proEtaleConstantRingAdjunction A g).unit.app M).val.app
              (Opposite.op V) x))) :
    a.hom ≫
        Functor.whiskerLeft (proEtaleConstantRingPullback A g)
          (openSquarePullbackModel A f).hom ≫
        Functor.whiskerRight (openSquarePullbackModel A g).hom (sfIntrinsicPullback A f) =
      (openSquarePullbackModel A (f ≫ g)).hom ≫
        (sfIntrinsicPullbackComp A f g).hom := by
  apply NatTrans.ext
  funext M
  apply ((proEtaleConstantRingAdjunction A (f ≫ g)).homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change
    ((a.hom.app M ≫
      (openSquarePullbackModel A f).hom.app ((proEtaleConstantRingPullback A g).obj M) ≫
      (sfIntrinsicPullback A f).map ((openSquarePullbackModel A g).hom.app M)).val.app
        (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V.unop)))
      (((proEtaleConstantRingAdjunction A (f ≫ g)).unit.app M).val.app V x) =
    (((openSquarePullbackModel A (f ≫ g)).hom.app M ≫
      (sfIntrinsicPullbackComp A f g).hom.app M).val.app
        (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V.unop)))
      (((proEtaleConstantRingAdjunction A (f ≫ g)).unit.app M).val.app V x)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [ha M V.unop x]
  erw [PresheafOfModules.naturality_apply]
  erw [PresheafOfModules.naturality_apply]
  erw [(openSquarePullbackModel_existsUnique A f).exists.choose_spec]
  have hn := (sfIntrinsicConstantModuleAdjunction f A).unit.naturality
    ((openSquarePullbackModel A g).hom.app M)
  have hv := congrArg (fun k ↦ k.val.app
    (Opposite.op ((proEtaleBaseChange g).obj V.unop))
      (((proEtaleConstantRingAdjunction A g).unit.app M).val.app V x)) hn
  dsimp only [Functor.comp_map, Functor.id_map,
    SheafOfModules.comp_val, PresheafOfModules.comp_app] at hv
  erw [← hv]
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [(openSquarePullbackModel_existsUnique A g).exists.choose_spec]
  erw [(openSquarePullbackModel_existsUnique A (f ≫ g)).exists.choose_spec]
  exact (intrinsic_comp_unit A f g M V.unop x).symm

private theorem ordinary_scalar_comp
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : proEtaleConstantRingPullback A (f ≫ g) ≅
      proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f)
    (ha : a.hom ≫
        Functor.whiskerLeft (proEtaleConstantRingPullback A g)
          (openSquarePullbackModel A f).hom ≫
        Functor.whiskerRight (openSquarePullbackModel A g).hom (sfIntrinsicPullback A f) =
      (openSquarePullbackModel A (f ≫ g)).hom ≫
        (sfIntrinsicPullbackComp A f g).hom)
    (M : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    a.hom.app ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
      (proEtaleConstantRingPullback A f).map
        ((Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Z A).functor
          (openSquarePullbackModel A g) ≪≫
          (sfIntrinsicModuleEquivalence Z A).funInvIdAssoc _).hom.app M) ≫
      (Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y A).functor
        (openSquarePullbackModel A f) ≪≫
        (sfIntrinsicModuleEquivalence Y A).funInvIdAssoc _).hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).obj M) =
      (Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Z A).functor
        (openSquarePullbackModel A (f ≫ g)) ≪≫
        (sfIntrinsicModuleEquivalence Z A).funInvIdAssoc _).hom.app M ≫
      (sfIntrinsicModuleEquivalence X A).functor.map
        ((ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).hom.app M) := by
  apply transport_square_comp
    (sfIntrinsicModuleEquivalence Z A) (sfIntrinsicModuleEquivalence Y A)
    (sfIntrinsicModuleEquivalence X A)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g))
    (proEtaleConstantRingPullback A g) (proEtaleConstantRingPullback A f)
    (proEtaleConstantRingPullback A (f ≫ g))
    (openSquarePullbackModel A g) (openSquarePullbackModel A f)
    (openSquarePullbackModel A (f ≫ g)) a
    (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g)
  intro N
  have h := congr_app ha N
  simpa only [sfIntrinsicPullback, sfIntrinsicTransport, Equivalence.unit,
    sfIntrinsicPullbackComp, sfIntrinsicTransportIso, sfIntrinsicTransportComp,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Equivalence.funInvIdAssoc_inv_app, Functor.comp_map, Iso.symm_hom, Category.assoc]
    using h

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor proEtaleRingModulePullback
  sfIntrinsicModuleEquivalence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finite_exact_comp (b : Base l E)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    let B := ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))
    (comparisonFiniteRealization l E b X n).map
        ((Functor.mapDerivedCategoryNatIso (upperStarComp B f g) ≪≫
          Functor.mapDerivedCategoryCompIso (upperStar B g) (upperStar B f)).inv.app L) ≫
      (Functor.mapDerivedCategorySquareIso
        (comparisonFiniteOrdinaryPull l E b (f ≫ g) n)).inv.app L =
    (Functor.mapDerivedCategorySquareIso
      (comparisonFiniteOrdinaryPull l E b f n)).inv.app
        ((upperStar B g).mapDerivedCategory.obj L) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) f).map
        ((Functor.mapDerivedCategorySquareIso
          (comparisonFiniteOrdinaryPull l E b g n)).inv.app L) ≫
      (proEtaleConstantRingPullbackComposition f g (R l E n)).hom.app
        ((comparisonFiniteRealization l E b Z n).obj L) := by
  let : Finite (R l E n) := b.finite n
  obtain ⟨a, ha, hD⟩ := proEtaleConstantRingPullbackComposition_ordinary f g (R l E n)
  have hs := ordinary_model_comp (R l E n) f g a ha
  have ho : Functor.whiskerLeft (sfIntrinsicModuleEquivalence Z (R l E n)).functor a.hom ≫
      Functor.whiskerRight (comparisonFiniteOrdinaryPull l E b g n).hom
        (proEtaleConstantRingPullback (R l E n) f) ≫
      Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) g)
        (comparisonFiniteOrdinaryPull l E b f n).hom =
    (comparisonFiniteOrdinaryPull l E b (f ≫ g) n).hom ≫
      Functor.whiskerRight
        (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f g).hom
        (sfIntrinsicModuleEquivalence X (R l E n)).functor := by
    apply NatTrans.ext
    funext M
    exact ordinary_scalar_comp (R l E n) f g a hs M
  have hd := derive_square_comp
    (sfIntrinsicModuleEquivalence Z (R l E n)).functor
    (sfIntrinsicModuleEquivalence Y (R l E n)).functor
    (sfIntrinsicModuleEquivalence X (R l E n)).functor
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) g)
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f)
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) (f ≫ g))
    (proEtaleConstantRingPullback (R l E n) g)
    (proEtaleConstantRingPullback (R l E n) f)
    (proEtaleConstantRingPullback (R l E n) (f ≫ g))
    (comparisonFiniteOrdinaryPull l E b g n)
    (comparisonFiniteOrdinaryPull l E b f n)
    (comparisonFiniteOrdinaryPull l E b (f ≫ g) n) a
    (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f g) ho
  rw [hD] at hd
  exact inverse_square_comp
    (sfIntrinsicModuleEquivalence Z (R l E n)).functor.mapDerivedCategory
    (sfIntrinsicModuleEquivalence Y (R l E n)).functor.mapDerivedCategory
    (sfIntrinsicModuleEquivalence X (R l E n)).functor.mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) g).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) (f ≫ g)).mapDerivedCategory
    (proEtaleConstantRingDerivedPullback (R l E n) g)
    (proEtaleConstantRingDerivedPullback (R l E n) f)
    (proEtaleConstantRingDerivedPullback (R l E n) (f ≫ g))
    (Functor.mapDerivedCategorySquareIso (comparisonFiniteOrdinaryPull l E b g n))
    (Functor.mapDerivedCategorySquareIso (comparisonFiniteOrdinaryPull l E b f n))
    (Functor.mapDerivedCategorySquareIso (comparisonFiniteOrdinaryPull l E b (f ≫ g) n))
    (proEtaleConstantRingPullbackComposition f g (R l E n)).symm
    (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f g) ≪≫
      Functor.mapDerivedCategoryCompIso
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) g)
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f)) hd L

-- Use the named comparisons through their component laws.

attribute [local irreducible] Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  Functor.leftDerivedFunctorIsoMapDerivedCategory comparisonFinitePull
  comparisonFiniteOrdinaryPull upperStar leftDerivedUpperStarComp
  leftDerivedUpperStarCompactificationIso

private theorem finite_pull_comp (b : Base l E)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonFiniteRealization l E b X n).map
        ((leftDerivedUpperStarComp
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f g).inv.app L) ≫
      (comparisonFinitePull l E b (f ≫ g) n).hom.app L =
    (comparisonFinitePull l E b f n).hom.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          g).leftDerivedFunctor.obj L) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) f).map
        ((comparisonFinitePull l E b g n).hom.app L) ≫
      (proEtaleConstantRingPullbackComposition f g (R l E n)).hom.app
        ((comparisonFiniteRealization l E b Z n).obj L) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))
  have hc : leftDerivedUpperStarComp B f g =
      (upperStar B (f ≫ g)).leftDerivedFunctorIsoMapDerivedCategory ≪≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp B f g) ≪≫
          Functor.mapDerivedCategoryCompIso (upperStar B g) (upperStar B f)) ≪≫
        Functor.isoWhiskerRight
          (upperStar B g).leftDerivedFunctorIsoMapDerivedCategory.symm
          (upperStar B f).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (upperStar B g).leftDerivedFunctor
          (upperStar B f).leftDerivedFunctorIsoMapDerivedCategory.symm := by
    simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, Iso.trans_assoc, Iso.symm_self_id_assoc]
  have h := derived_rebase_square_comp
    (upperStar B g).mapDerivedCategory (upperStar B g).leftDerivedFunctor
    (upperStar B f).mapDerivedCategory (upperStar B f).leftDerivedFunctor
    (upperStar B (f ≫ g)).mapDerivedCategory (upperStar B (f ≫ g)).leftDerivedFunctor
    (upperStar B g).leftDerivedFunctorIsoMapDerivedCategory
    (upperStar B f).leftDerivedFunctorIsoMapDerivedCategory
    (upperStar B (f ≫ g)).leftDerivedFunctorIsoMapDerivedCategory
    (comparisonFiniteRealization l E b Z n)
    (comparisonFiniteRealization l E b Y n)
    (comparisonFiniteRealization l E b X n)
    (proEtaleConstantRingDerivedPullback (R l E n) g)
    (proEtaleConstantRingDerivedPullback (R l E n) f)
    (proEtaleConstantRingDerivedPullback (R l E n) (f ≫ g))
    (Functor.mapDerivedCategorySquareIso (comparisonFiniteOrdinaryPull l E b g n))
    (Functor.mapDerivedCategorySquareIso (comparisonFiniteOrdinaryPull l E b f n))
    (Functor.mapDerivedCategorySquareIso (comparisonFiniteOrdinaryPull l E b (f ≫ g) n))
    (proEtaleConstantRingPullbackComposition f g (R l E n)).symm
    (Functor.mapDerivedCategoryNatIso (upperStarComp B f g) ≪≫
      Functor.mapDerivedCategoryCompIso (upperStar B g) (upperStar B f))
    (fun M ↦ finite_exact_comp l E b f g n M) L
  have hc' := congrArg (fun e : (upperStar B (f ≫ g)).leftDerivedFunctor ≅
      (upperStar B g).leftDerivedFunctor ⋙ (upperStar B f).leftDerivedFunctor ↦
    (comparisonFiniteRealization l E b X n).map (e.inv.app L) ≫
      (comparisonFinitePull l E b (f ≫ g) n).hom.app L) hc
  exact hc'.trans (by simpa only [comparisonFinitePull, Iso.symm_inv] using h)

private theorem finite_compactification_iso_def
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    leftDerivedUpperStarCompactificationIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c =
      (leftDerivedUpperStarComp
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c.i c.g).symm ≪≫
        eqToIso (congrArg
          (fun h : X ⟶ Y ↦
            (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              h).leftDerivedFunctor) c.comm.symm) := by
  unfold leftDerivedUpperStarCompactificationIso
  rfl

-- Eliminate the factorization equality before specializing the compactification data.
private theorem finite_factorization_pull_comp (b : Base l E)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y}
    (i : X ⟶ Z) (g : Z ⟶ Y) (h : i ≫ g = f) (n : ℕ)
    (I : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
      g).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          i).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor)
    (hi : I = (leftDerivedUpperStarComp
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) i g).symm ≪≫
        eqToIso (congrArg (fun q : X ⟶ Y ↦
          (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
            q).leftDerivedFunctor) h))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonFiniteRealization l E b X n).map
      (I.hom.app L) ≫
      (comparisonFinitePull l E b f n).hom.app L =
    (comparisonFinitePull l E b i n).hom.app
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
        g).leftDerivedFunctor.obj L) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) i).map
        ((comparisonFinitePull l E b g n).hom.app L) ≫
      (((proEtaleConstantRingPullbackComposition i g (R l E n)).hom ≫
        eqToHom (congrArg
          (fun h ↦ proEtaleConstantRingDerivedPullback (R l E n) h)
            h)).app ((comparisonFiniteRealization l E b Y n).obj L)) := by
  cases h
  simp only [eqToIso_refl, Iso.trans_refl] at hi
  subst I
  simpa only [Iso.symm_hom, eqToHom_refl, Category.comp_id] using
    finite_pull_comp l E b i g n L

private theorem compactification_pull_comp (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (n : ℕ)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonFiniteRealization l E b X n).map
      ((leftDerivedUpperStarCompactificationIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).hom.app L) ≫
      (comparisonFinitePull l E b f n).hom.app L =
    (comparisonFinitePull l E b c.i n).hom.app
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
        c.g).leftDerivedFunctor.obj L) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) c.i).map
        ((comparisonFinitePull l E b c.g n).hom.app L) ≫
      (((proEtaleConstantRingPullbackComposition c.i c.g (R l E n)).hom ≫
        eqToHom (congrArg
          (fun h ↦ proEtaleConstantRingDerivedPullback (R l E n) h)
            c.comm.symm)).app ((comparisonFiniteRealization l E b Y n).obj L)) := by
  exact finite_factorization_pull_comp l E b c.i c.g c.comm.symm n
    (leftDerivedUpperStarCompactificationIso
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c)
    (finite_compactification_iso_def l E c n) L

/-- Pullback coordinates respect the compactification compositor.
Source: blueprint operations proof (2), scalar-coordinate compositor square.
(blueprint: new-lem-sp-strict-finite-open-projection-pull-composition).
Proof: expand comparisonFiniteOrdinaryPull. The scalar equivalence unit and
counit cancel in the composite; on inverse-image unit sections the remaining
maps are the same iterated unit. The inverse-image universal property identifies
the two ordinary composites. Localize this equality and expand the native
leftDerivedUpperStarCompactificationIso. Cancel the exact/left-derived factors
and transport c.comm, obtaining the displayed equality. This calculation has
no tensor or open projection map and applies also to identity factors and empty
schemes. -/
theorem strictFiniteOpenProjectionPullComposition (b : Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (n : ℕ)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonFiniteRealization l E b X n).map
      ((leftDerivedUpperStarCompactificationIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).hom.app L) ≫
      (comparisonFinitePull l E b f n).hom.app L =
    (comparisonFinitePull l E b c.i n).hom.app
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
        c.g).leftDerivedFunctor.obj L) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) c.i).map
        ((comparisonFinitePull l E b c.g n).hom.app L) ≫
      (((proEtaleConstantRingPullbackComposition c.i c.g (R l E n)).hom ≫
        eqToHom (congrArg
          (fun h ↦ proEtaleConstantRingDerivedPullback (R l E n) h)
            c.comm.symm)).app ((comparisonFiniteRealization l E b Y n).obj L)) := by
  exact compactification_pull_comp l E b c n L

end AlgebraicGeometry.ProEtale.SpTowerShriek
