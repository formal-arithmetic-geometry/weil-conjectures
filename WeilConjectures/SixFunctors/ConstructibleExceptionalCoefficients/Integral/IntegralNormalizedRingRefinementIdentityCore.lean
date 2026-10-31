/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import all WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import all WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.FlatScalarTowerCoherence

/-! # Identity normalization of the ambient proper/open refinement word

The compatibility equation fixes the coefficient identity. Sectionwise direct-image
unit laws pass to inverse images by adjunction, then to derived functors by localization.
The normalized open transpose and the proper compositor consequently cancel.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction
namespace WeilConjectures.ConstructibleExceptionalCoefficients

private abbrev ringAdj {U V : Scheme.{w}} (j : U ⟶ V) :=
  proEtaleSheafAdjunction j CommRingCat.{w + 1}

-- The ring inverse-image identity is the mate of the site identity.
private theorem ring_pull_left_unit {U V : Scheme.{w}} (j : U ⟶ V) :
    (proEtaleRingInverseImageComp (𝟙 U) j).hom ≫
      Functor.whiskerLeft (proEtaleSheafInverseImage j CommRingCat.{w + 1})
        (proEtaleRingInverseImageId U).hom =
      eqToHom (congrArg
        (fun g ↦ proEtaleSheafInverseImage g CommRingCat.{w + 1})
        (Category.id_comp j)) := by
  let q := AlgebraicGeometry.ProEtale.lowerStarComp CommRingCat.{w + 1} (𝟙 U) j ≪≫
    eqToIso (congrArg
      (fun g ↦ proEtaleSheafDirectImage g CommRingCat.{w + 1}) (Category.id_comp j))
  have hq : q = Functor.isoWhiskerRight
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{w + 1} U)
      (proEtaleSheafDirectImage j CommRingCat.{w + 1}) ≪≫
        Functor.leftUnitor _ := by
    dsimp only [q]
    rw [AlgebraicGeometry.ProEtale.legacy_lowerStarComp_id_left]
    ext M T
    simp [AlgebraicGeometry.ProEtale.lowerStarCongr]
    rfl
  have hc {a b : U ⟶ V} (e : a = b) :
      conjugateIsoEquiv (ringAdj b) (ringAdj a)
        (eqToIso (congrArg (fun g ↦ proEtaleSheafInverseImage g CommRingCat.{w + 1}) e)) =
      (eqToIso (congrArg (fun g ↦ proEtaleSheafDirectImage g CommRingCat.{w + 1}) e)).symm := by
    cases e
    ext : 1
    simp
  suffices he : proEtaleRingInverseImageComp (𝟙 U) j ≪≫
      Functor.isoWhiskerLeft (proEtaleSheafInverseImage j CommRingCat.{w + 1})
        (proEtaleRingInverseImageId U) ≪≫ Functor.rightUnitor _ =
      eqToIso (congrArg
        (fun g ↦ proEtaleSheafInverseImage g CommRingCat.{w + 1}) (Category.id_comp j)) by
    have he' := congrArg Iso.hom he
    apply NatTrans.ext
    funext M
    have heM := NatTrans.congr_app he' M
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at heM
    erw [Category.comp_id] at heM
    exact heM
  apply (conjugateIsoEquiv (ringAdj j) (ringAdj (𝟙 U ≫ j))).injective
  rw [conjugateIsoEquiv_trans _ ((ringAdj j).comp (ringAdj (𝟙 U))) _,
    conjugateIsoEquiv_trans _ ((ringAdj j).comp Adjunction.id) _,
    conjugateIsoEquiv_rightUnitor, conjugateIsoEquiv_isoWhiskerLeft,
    hc (Category.id_comp j)]
  simp only [proEtaleRingInverseImageComp, proEtaleRingInverseImageId,
    conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]
  change (Functor.isoWhiskerRight
    (ProEtale.lowerStarId CommRingCat.{w + 1} U)
    (proEtaleSheafDirectImage j CommRingCat.{w + 1}) ≪≫ Functor.leftUnitor _).symm ≪≫
      ProEtale.lowerStarComp CommRingCat.{w + 1} (𝟙 U) j = _
  rw [← hq]
  apply Iso.ext
  simp only [q, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

-- No global coherence of R is available: hg itself forces its identity comparison.
private theorem coefficient_identity (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V)
    (hg : R.pull (𝟙 U ≫ g) = proEtaleRingCompositeCoefficients (𝟙 U) g
      (R.ring V) (R.ring U) (R.ring U) (R.pull g) (R.pull (𝟙 U))) :
    R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U) := by
  apply Iso.ext
  apply (cancel_epi ((proEtaleRingInverseImageComp (𝟙 U) g).hom.app (R.ring V) ≫
    (proEtaleSheafInverseImage (𝟙 U) CommRingCat.{w + 1}).map (R.pull g).hom)).mp
  have hh := congrArg Iso.hom hg
  dsimp only [proEtaleRingCompositeCoefficients, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom] at hh
  simp only [Category.assoc, Iso.app_hom]
  rw [← hh]
  have hn := (proEtaleRingInverseImageId U).hom.naturality (R.pull g).hom
  dsimp only [Functor.id_map, Functor.id_obj] at hn
  erw [hn]
  rw [← Category.assoc]
  have hu := NatTrans.congr_app (ring_pull_left_unit g) (R.ring V)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
  rw [hu]
  have he {a b : U ⟶ V} (e : a = b) :
      (eqToHom (congrArg
        (fun j ↦ proEtaleSheafInverseImage j CommRingCat.{w + 1}) e)).app (R.ring V) ≫
        (R.pull b).hom = (R.pull a).hom := by
    cases e
    simp
  exact (he (Category.id_comp g)).symm

private def modulePushId (R : PurCompactSupport.Coefficients.{w}) (U : Scheme.{w})
    (hid : R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U)) :
    proEtaleRingModuleDirectImage (𝟙 U) (R.ring U) (R.ring U) (R.pull (𝟙 U)) ≅
      𝟭 (pbcModules U (R.ring U)) := by
  have hr : proEtaleRingDirectImageMap (𝟙 U) (R.ring U) (R.ring U) (R.pull (𝟙 U)) =
      (ProEtale.lowerStarId CommRingCat.{w + 1} U).inv.app (R.ring U) := by
    rw [proEtaleRingDirectImageMap, hid]
    exact (unit_conjugateEquiv_symm Adjunction.id (ringAdj (𝟙 U))
      (ProEtale.lowerStarId CommRingCat.{w + 1} U).inv (R.ring U)).symm
  unfold proEtaleRingModuleDirectImage
  refine SheafOfModules.pushforwardCongr₂
    (J := ProEt.topology U) (K := ProEt.topology U)
    (F := 𝟭 U.ProEt) (G := proEtaleBaseChange (𝟙 U)) (ψ := 𝟙 _) _
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).symm ?_ ≪≫
      SheafOfModules.pushforwardId _
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext T
  change (forget₂ CommRingCat.{w + 1} RingCat.{w + 1}).map
    ((proEtaleRingDirectImageMap (𝟙 U) (R.ring U) (R.ring U) (R.pull (𝟙 U))).hom.app T) ≫ _ = _
  rw [hr]
  ext x
  change ((R.ring U).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app T.unop).op)
    (((R.ring U).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).hom.app T.unop).op) x) = x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
  rfl

private abbrev modulePush (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V) :=
  proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)

private theorem modulePushCongr_sections (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} {g h : U ⟶ V} (e : g = h)
    (N : pbcModules U (R.ring U)) (T : V.ProEt)
    (m : ((modulePush R g).obj N).val.obj (Opposite.op T)) :
    ((eqToIso (congrArg (fun a ↦ modulePush R a) e)).hom.app N).val.app
        (Opposite.op T) m =
      N.val.map ((MorphismProperty.Over.pullbackCongr
        (P := @WeaklyEtale) (Q := ⊤) e.symm).hom.app T).op m := by
  cases e
  erw [MorphismProperty.Over.pullbackCongr_refl g]
  change m = N.val.presheaf.map (𝟙 _) m
  rw [N.val.presheaf.map_id]
  rfl

private theorem modulePushId_sections (R : PurCompactSupport.Coefficients.{w})
    (U : Scheme.{w})
    (hid : R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U))
    (N : pbcModules U (R.ring U)) (T : U.ProEt)
    (m : ((modulePush R (𝟙 U)).obj N).val.obj (Opposite.op T)) :
    ((modulePushId R U hid).hom.app N).val.app (Opposite.op T) m =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app T).op m := by
  dsimp only [modulePushId, SheafOfModules.pushforwardCongr₂, Iso.trans_hom,
    NatTrans.comp_app, SheafOfModules.pushforwardId, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, SheafOfModules.pushforwardNatIso_hom]
  erw [SheafOfModules.pushforwardCongr_hom_app_val_app]
  rfl

private theorem site_congr_transport {U V : Scheme.{w}} {g h : U ⟶ V} (e : g = h) :
    MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) e =
      eqToIso (congrArg proEtaleBaseChange e) := by
  cases e
  exact MorphismProperty.Over.pullbackCongr_refl g rfl

private theorem site_left_unit {U V : Scheme.{w}} (g : U ⟶ V) (T : V.ProEt) :
    (MorphismProperty.Over.pullbackCongr
        (P := @WeaklyEtale) (Q := ⊤) (Category.id_comp g).symm).hom.app T ≫
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
        (𝟙 U) g).hom.app T =
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app
      ((proEtaleBaseChange g).obj T) := by
  have h := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_left
      (P := @WeaklyEtale) (Q := ⊤) g (𝟙 U ≫ g) rfl)) T
  rw [site_congr_transport] at h
  rw [site_congr_transport]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app] at h ⊢
  rw [h]
  simp

private theorem site_right_unit {U V : Scheme.{w}} (g : U ⟶ V) (T : V.ProEt) :
    (MorphismProperty.Over.pullbackCongr
        (P := @WeaklyEtale) (Q := ⊤) (Category.comp_id g).symm).hom.app T ≫
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
        g (𝟙 V)).hom.app T =
    (proEtaleBaseChange g).map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ V).inv.app T) := by
  have h := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_right
      (P := @WeaklyEtale) (Q := ⊤) g (g ≫ 𝟙 V) rfl)) T
  rw [site_congr_transport] at h
  rw [site_congr_transport]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, eqToIso.hom, eqToHom_app] at h ⊢
  rw [h]
  simp

-- The chosen compositor is fixed on sections, so the site unit laws determine it.
private theorem modulePush_left_unit (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V)
    (hg : R.pull (𝟙 U ≫ g) = proEtaleRingCompositeCoefficients (𝟙 U) g
      (R.ring V) (R.ring U) (R.ring U) (R.pull g) (R.pull (𝟙 U)))
    (hid : R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U)) :
    (PurCompactSupport.modulePushComposition_existsUnique R (𝟙 U) g hg).exists.choose ≪≫
      eqToIso (congrArg (fun a ↦ modulePush R a) (Category.id_comp g)) =
    Functor.isoWhiskerRight (modulePushId R U hid) (modulePush R g) ≪≫
      Functor.leftUnitor _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  change ((eqToIso (congrArg (fun a ↦ modulePush R a) (Category.id_comp g))).hom.app N).val.app
      T ((((PurCompactSupport.modulePushComposition_existsUnique
        R (𝟙 U) g hg).exists.choose).hom.app N).val.app T m) =
    ((modulePushId R U hid).hom.app N).val.app ((proEtaleBaseChange g).op.obj T) m
  rw [modulePushCongr_sections R (Category.id_comp g)]
  rw [(PurCompactSupport.modulePushComposition_existsUnique R (𝟙 U) g hg).exists.choose_spec]
  rw [modulePushId_sections]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, site_left_unit]
  rfl

private theorem modulePush_right_unit (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V)
    (hg : R.pull (g ≫ 𝟙 V) = proEtaleRingCompositeCoefficients g (𝟙 V)
      (R.ring V) (R.ring V) (R.ring U) (R.pull (𝟙 V)) (R.pull g))
    (hid : R.pull (𝟙 V) = (proEtaleRingInverseImageId V).app (R.ring V)) :
    (PurCompactSupport.modulePushComposition_existsUnique R g (𝟙 V) hg).exists.choose ≪≫
      eqToIso (congrArg (fun a ↦ modulePush R a) (Category.comp_id g)) =
    Functor.isoWhiskerLeft (modulePush R g) (modulePushId R V hid) ≪≫
      Functor.rightUnitor _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  change ((eqToIso (congrArg (fun a ↦ modulePush R a) (Category.comp_id g))).hom.app N).val.app
      T ((((PurCompactSupport.modulePushComposition_existsUnique
        R g (𝟙 V) hg).exists.choose).hom.app N).val.app T m) =
    ((modulePushId R V hid).hom.app ((modulePush R g).obj N)).val.app T m
  rw [modulePushCongr_sections R (Category.comp_id g)]
  rw [(PurCompactSupport.modulePushComposition_existsUnique R g (𝟙 V) hg).exists.choose_spec]
  rw [modulePushId_sections]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, site_right_unit]
  rfl

private theorem conjugate_index_iso
    {I : Type*} {C D : Type*} [Category C] [Category D]
    (L : I → C ⥤ D) (P : I → D ⥤ C) (ad : ∀ i, L i ⊣ P i)
    {i j : I} (h : i = j) :
    conjugateIsoEquiv (ad j) (ad i) (eqToIso (congrArg L h)) =
      (eqToIso (congrArg P h)).symm := by
  cases h
  ext : 1
  simp

private theorem pull_left_unit_of_push
    {I : Type*} {C D : Type*} [Category C] [Category D]
    (L : I → C ⥤ D) (P : I → D ⥤ C) (ad : ∀ i, L i ⊣ P i)
    {i j : I} (h : i = j) {L₀ P₀ : D ⥤ D} (a₀ : L₀ ⊣ P₀)
    (e : P₀ ≅ 𝟭 D) (c : L i ≅ L j ⋙ L₀)
    (hq : conjugateIsoEquiv ((ad j).comp a₀) (ad i) c ≪≫
      eqToIso (congrArg P h) =
        Functor.isoWhiskerRight e (P j) ≪≫ Functor.leftUnitor (P j)) :
    c.symm ≪≫ eqToIso (congrArg L h) =
      Functor.isoWhiskerLeft (L j) (Adjunction.leftAdjointIdIso a₀ e) ≪≫
        Functor.rightUnitor (L j) := by
  have he : c.symm ≪≫ eqToIso (congrArg L h) =
      Adjunction.leftAdjointCompIso (ad j) a₀ (ad j)
        (conjugateIsoEquiv ((ad j).comp a₀) (ad i) c ≪≫ eqToIso (congrArg P h)) := by
    apply (conjugateIsoEquiv (ad j) ((ad j).comp a₀)).injective
    rw [conjugateIsoEquiv_trans _ (ad i) _, conjugate_index_iso L P ad h]
    simp only [Adjunction.leftAdjointCompIso, Equiv.apply_symm_apply, Iso.trans_symm]
    rfl
  rw [he]
  exact Adjunction.leftAdjointCompIso_comp_id (ad j) a₀ _ e hq

private theorem pull_right_unit_of_push
    {I : Type*} {C D : Type*} [Category C] [Category D]
    (L : I → C ⥤ D) (P : I → D ⥤ C) (ad : ∀ i, L i ⊣ P i)
    {i j : I} (h : i = j) {L₀ P₀ : C ⥤ C} (a₀ : L₀ ⊣ P₀)
    (e : P₀ ≅ 𝟭 C) (c : L i ≅ L₀ ⋙ L j)
    (hq : conjugateIsoEquiv (a₀.comp (ad j)) (ad i) c ≪≫
      eqToIso (congrArg P h) =
        Functor.isoWhiskerLeft (P j) e ≪≫ Functor.rightUnitor (P j)) :
    c.symm ≪≫ eqToIso (congrArg L h) =
      Functor.isoWhiskerRight (Adjunction.leftAdjointIdIso a₀ e) (L j) ≪≫
        Functor.leftUnitor (L j) := by
  have he : c.symm ≪≫ eqToIso (congrArg L h) =
      Adjunction.leftAdjointCompIso a₀ (ad j) (ad j)
        (conjugateIsoEquiv (a₀.comp (ad j)) (ad i) c ≪≫ eqToIso (congrArg P h)) := by
    apply (conjugateIsoEquiv (ad j) (a₀.comp (ad j))).injective
    rw [conjugateIsoEquiv_trans _ (ad i) _, conjugate_index_iso L P ad h]
    simp only [Adjunction.leftAdjointCompIso, Equiv.apply_symm_apply, Iso.trans_symm]
    rfl
  rw [he]
  exact Adjunction.leftAdjointCompIso_id_comp a₀ (ad j) _ e hq

private abbrev modulePull (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V) :=
  proEtaleRingModulePullback g (R.ring V) (R.ring U) (R.pull g)

private abbrev moduleAdj (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V) :=
  proEtaleRingModuleAdjunction g (R.ring V) (R.ring U) (R.pull g)

private def modulePullId (R : PurCompactSupport.Coefficients.{w}) (U : Scheme.{w})
    (hid : R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U)) :
    modulePull R (𝟙 U) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso (moduleAdj R (𝟙 U)) (modulePushId R U hid)

private def modulePullComp (R : PurCompactSupport.Coefficients.{w})
    {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    modulePull R (h ≫ k) ≅ modulePull R k ⋙ modulePull R h :=
  (conjugateIsoEquiv ((moduleAdj R k).comp (moduleAdj R h))
    (moduleAdj R (h ≫ k))).symm
      (PurCompactSupport.modulePushComposition_existsUnique R h k hc).exists.choose

private theorem modulePull_left_unit (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V)
    (hg : R.pull (𝟙 U ≫ g) = proEtaleRingCompositeCoefficients (𝟙 U) g
      (R.ring V) (R.ring U) (R.ring U) (R.pull g) (R.pull (𝟙 U)))
    (hid : R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U)) :
    (modulePullComp R (𝟙 U) g hg).symm ≪≫
      eqToIso (congrArg (fun a ↦ modulePull R a) (Category.id_comp g)) =
    Functor.isoWhiskerLeft (modulePull R g) (modulePullId R U hid) ≪≫
      Functor.rightUnitor _ := by
  apply pull_left_unit_of_push (fun a : U ⟶ V ↦ modulePull R a)
    (fun a ↦ modulePush R a) (fun a ↦ moduleAdj R a) (Category.id_comp g)
    (moduleAdj R (𝟙 U)) (modulePushId R U hid)
  simpa only [modulePullComp, Equiv.apply_symm_apply] using modulePush_left_unit R g hg hid

private theorem modulePull_right_unit (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V)
    (hg : R.pull (g ≫ 𝟙 V) = proEtaleRingCompositeCoefficients g (𝟙 V)
      (R.ring V) (R.ring V) (R.ring U) (R.pull (𝟙 V)) (R.pull g))
    (hid : R.pull (𝟙 V) = (proEtaleRingInverseImageId V).app (R.ring V)) :
    (modulePullComp R g (𝟙 V) hg).symm ≪≫
      eqToIso (congrArg (fun a ↦ modulePull R a) (Category.comp_id g)) =
    Functor.isoWhiskerRight (modulePullId R V hid) (modulePull R g) ≪≫
      Functor.leftUnitor _ := by
  apply pull_right_unit_of_push (fun a : U ⟶ V ↦ modulePull R a)
    (fun a ↦ modulePush R a) (fun a ↦ moduleAdj R a) (Category.comp_id g)
    (moduleAdj R (𝟙 V)) (modulePushId R V hid)
  simpa only [modulePullComp, Equiv.apply_symm_apply] using modulePush_right_unit R g hg hid

private def derivedPullId (R : PurCompactSupport.Coefficients.{w}) (U : Scheme.{w})
    (hid : R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U)) :
    PurCompactSupport.pull R (𝟙 U) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (modulePullId R U hid) ≪≫
    Functor.mapDerivedCategoryIdIso _

-- Exact localization preserves these specified unit comparisons.
private theorem derivedPull_left_unit (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V)
    (hg : R.pull (𝟙 U ≫ g) = proEtaleRingCompositeCoefficients (𝟙 U) g
      (R.ring V) (R.ring U) (R.ring U) (R.pull g) (R.pull (𝟙 U)))
    (hid : R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U))
    (M : DerivedCategory (pbcModules V (R.ring V))) :
    (PurCompactSupport.geometricPullComposition R (𝟙 U) g hg).inv.app M ≫
      (eqToIso (congrArg (fun a ↦ PurCompactSupport.pull R a) (Category.id_comp g))).hom.app M =
    (derivedPullId R U hid).hom.app ((PurCompactSupport.pull R g).obj M) := by
  have ha (N : pbcModules V (R.ring V)) := NatTrans.congr_app
    (congrArg Iso.hom (modulePull_left_unit R g hg hid)) N
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app] at ha
  exact CategoryTheory.Mod.derive_right_unit (modulePull R g) (modulePull R (𝟙 U ≫ g))
    (modulePull R (𝟙 U)) (modulePullId R U hid) (modulePullComp R (𝟙 U) g hg)
    (congrArg (fun a ↦ modulePull R a) (Category.id_comp g)) ha M

-- Exact-functor localization, as in StrictTowerProperOpenCalculus. Keeping the
-- transport isomorphism explicit avoids unfolding transported functor instances.
private theorem derive_unit_right_iso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F H : C ⥤ D) (I : C ⥤ C)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (a : H ≅ I ⋙ F) (e : I ≅ 𝟭 C) (b : H ≅ F)
    (ha : a.hom ≫ Functor.whiskerRight e.hom F = b.hom) :
    (Functor.mapDerivedCategoryNatIso a).hom ≫
        (Functor.mapDerivedCategoryCompIso I F).hom ≫
        Functor.whiskerRight
          ((Functor.mapDerivedCategoryNatIso e).hom ≫
            (Functor.mapDerivedCategoryIdIso C).hom) F.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso b).hom := by
  have he : a ≪≫ Functor.isoWhiskerRight e F = b := Iso.ext ha
  have h := congrArg (fun c ↦ (Functor.mapDerivedCategoryNatIso c).hom) he
  rw [Functor.mapDerivedCategoryNatIso_trans] at h
  have hn := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F
  have hu := Functor.mapDerivedCategoryCompIso_id_comp F
  apply NatTrans.ext
  funext N
  have hN := congr_app h N
  have hnN := congr_app hn N
  have huN := congr_app hu N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app,
    Functor.map_comp] at *
  rw [← reassoc_of% hnN, huN]
  erw [Category.comp_id]
  exact hN

-- The identity mate calculation of CompactSupportIdentityCalculus, with arbitrary
-- category universes so that it also applies to these ambient derived categories.
private theorem identity_comparison_general
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {L : D ⥤ D} (h : F' = F) (τ : F' ⟶ F ⋙ L)
    (idIso : L ≅ 𝟭 D)
    (hτ : ∀ M, τ.app M ≫ idIso.hom.app (F.obj M) =
      eqToHom (congrArg (fun V : C ⥤ D ↦ V.obj M) h)) :
    eqToHom h.symm ≫ τ = (Functor.rightUnitor F).inv ≫
      Functor.whiskerLeft F idIso.inv := by
  subst h
  ext M
  apply (cancel_mono (idIso.hom.app (F'.obj M))).1
  simpa only [NatTrans.comp_app, eqToHom_refl, NatTrans.id_app,
    Category.id_comp, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app, Functor.id_obj] using hτ M

private theorem conjugate_index_eq_general
    {I : Type*} {C D : Type*} [Category C] [Category D]
    (L : I → C ⥤ D) (R : I → D ⥤ C) (ad : ∀ i, L i ⊣ R i)
    {i j : I} (h : i = j) :
    conjugateEquiv (ad i) (ad j) (eqToHom (congrArg L h.symm)) =
      eqToHom (congrArg R h) := by
  subst h
  simp

private theorem conjugate_rightUnitor_inv_general
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (ad : F ⊣ G) :
    conjugateEquiv (ad.comp Adjunction.id) ad (Functor.rightUnitor F).inv =
      (Functor.leftUnitor G).hom := by
  have h : conjugateIsoEquiv ad (ad.comp Adjunction.id) (Functor.rightUnitor F) =
      (Functor.leftUnitor G).symm := by
    apply Iso.ext
    exact conjugateEquiv_rightUnitor_hom ad
  exact congrArg Iso.inv h

private theorem conjugate_identity_comp_general
    {C D : Type*} [Category C] [Category D]
    {L R : D ⥤ D} (ad : L ⊣ R) (idIso : L ≅ 𝟭 D)
    {F : C ⥤ D} {G : D ⥤ C} (ag : F ⊣ G) :
    conjugateEquiv (ag.comp ad) ag
        ((Functor.rightUnitor F).inv ≫ Functor.whiskerLeft F idIso.inv) =
      Functor.whiskerRight (conjugateEquiv ad Adjunction.id idIso.inv) G ≫
        (Functor.leftUnitor G).hom := by
  rw [← conjugateEquiv_comp (ag.comp ad) (ag.comp Adjunction.id) ag,
    conjugateEquiv_whiskerLeft, conjugate_rightUnitor_inv_general]

private theorem conjugate_paste_identity_general
    {I : Type*} {C D : Type*} [Category C] [Category D]
    (L : I → C ⥤ D) (R : I → D ⥤ C) (ad : ∀ i, L i ⊣ R i)
    {i j : I} (h : i = j) {L₀ R₀ : D ⥤ D} (ai : L₀ ⊣ R₀)
    (idIso : L₀ ≅ 𝟭 D) (τ : L i ⟶ L j ⋙ L₀)
    (hn : eqToHom (congrArg L h.symm) ≫ τ =
      (Functor.rightUnitor (L j)).inv ≫ Functor.whiskerLeft (L j) idIso.inv)
    (M : D) :
    (conjugateEquiv ((ad j).comp ai) (ad i) τ).app M ≫
        (eqToHom (congrArg R h)).app M =
      (R j).map ((conjugateEquiv ai Adjunction.id idIso.inv).app M) := by
  rw [← conjugate_index_eq_general L R ad h]
  have hc := NatTrans.congr_app
    (conjugateEquiv_comp ((ad j).comp ai) (ad i) (ad j) τ
      (eqToHom (congrArg L h.symm))) M
  rw [show (conjugateEquiv ((ad j).comp ai) (ad i) τ).app M ≫
      (conjugateEquiv (ad i) (ad j) (eqToHom (congrArg L h.symm))).app M =
      (conjugateEquiv ((ad j).comp ai) (ad j)
        (eqToHom (congrArg L h.symm) ≫ τ)).app M from hc]
  rw [hn, conjugate_identity_comp_general]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact Category.comp_id _

private abbrev derivedAdj (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V) :=
  proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)

private theorem derivedPull_left_unit_forward (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V)
    (hg : R.pull (𝟙 U ≫ g) = proEtaleRingCompositeCoefficients (𝟙 U) g
      (R.ring V) (R.ring U) (R.ring U) (R.pull g) (R.pull (𝟙 U)))
    (hid : R.pull (𝟙 U) = (proEtaleRingInverseImageId U).app (R.ring U))
    (M : DerivedCategory (pbcModules V (R.ring V))) :
    (PurCompactSupport.geometricPullComposition R (𝟙 U) g hg).hom.app M ≫
      (derivedPullId R U hid).hom.app ((PurCompactSupport.pull R g).obj M) =
    eqToHom (congrArg (fun a ↦ (PurCompactSupport.pull R a).obj M)
      (Category.id_comp g)) := by
  rw [← derivedPull_left_unit R g hg hid M, ← Category.assoc]
  simp only [Iso.hom_inv_id_app, Category.id_comp, eqToIso.hom, eqToHom_app]

private theorem derived_transport (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} {g h : U ⟶ V} (e : g = h) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (fun a ↦ modulePull R a) e))).hom =
    (eqToIso (congrArg (fun a ↦ PurCompactSupport.pull R a) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem derivedPull_right_unit_forward (R : PurCompactSupport.Coefficients.{w})
    {U V : Scheme.{w}} (g : U ⟶ V)
    (hg : R.pull (g ≫ 𝟙 V) = proEtaleRingCompositeCoefficients g (𝟙 V)
      (R.ring V) (R.ring V) (R.ring U) (R.pull (𝟙 V)) (R.pull g))
    (hid : R.pull (𝟙 V) = (proEtaleRingInverseImageId V).app (R.ring V))
    (M : DerivedCategory (pbcModules V (R.ring V))) :
    (PurCompactSupport.geometricPullComposition R g (𝟙 V) hg).hom.app M ≫
      (PurCompactSupport.pull R g).map ((derivedPullId R V hid).hom.app M) =
    eqToHom (congrArg (fun a ↦ (PurCompactSupport.pull R a).obj M)
      (Category.comp_id g)) := by
  have ha : (modulePullComp R g (𝟙 V) hg).hom ≫
      Functor.whiskerRight (modulePullId R V hid).hom (modulePull R g) =
      (eqToIso (congrArg (fun a ↦ modulePull R a) (Category.comp_id g))).hom := by
    apply NatTrans.ext
    funext N
    have hn₀ := NatTrans.congr_app (congrArg Iso.hom
      (modulePull_right_unit R g hg hid)) N
    dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app] at hn₀
    have hn := hn₀.trans (Category.comp_id _)
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app]
    rw [← hn, ← Category.assoc]
    simp only [Iso.hom_inv_id_app, Category.id_comp]
  have ht := derive_unit_right_iso (modulePull R g) (modulePull R (g ≫ 𝟙 V))
    (modulePull R (𝟙 V)) (modulePullComp R g (𝟙 V) hg) (modulePullId R V hid)
    (eqToIso (congrArg (fun a ↦ modulePull R a) (Category.comp_id g))) ha
  rw [derived_transport R (Category.comp_id g)] at ht
  have hM := congr_app ht M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, ← Category.assoc,
    eqToIso.hom, eqToHom_app] at hM
  exact hM

/--
The proper/open word for an identity compactification is the identity when its open
comparison has the prescribed adjunction transpose.  This is the ambient categorical
calculation used by the integral refinement identity component.

Source: the identity diagram in the integral normalized refinement pasting argument
(blueprint: lem-sf-integral-normalized-ring-refinement-identity-component).
Proof: expand the transpose through the open adjunction, use its triangle identity,
and use the left-unit law for the proper direct-image compositor.  The resulting
composite is the identity on the compact-support image object.
-/
theorem integral_normalized_ring_refinement_identity_core
    (R : PurCompactSupport.Coefficients.{max u v})
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    {c : Compactification f}
    (hi : R.pull (c.i ≫ (Compactification.Refinement.id c).hom) =
      proEtaleRingCompositeCoefficients c.i (Compactification.Refinement.id c).hom
        (R.ring c.Z) (R.ring c.Z) (R.ring X)
        (R.pull (Compactification.Refinement.id c).hom) (R.pull c.i))
    (hg : R.pull ((Compactification.Refinement.id c).hom ≫ c.g) =
      proEtaleRingCompositeCoefficients (Compactification.Refinement.id c).hom c.g
        (R.ring Y) (R.ring c.Z) (R.ring c.Z)
        (R.pull c.g) (R.pull (Compactification.Refinement.id c).hom))
    (K : DerivedCategory (pbcModules X (R.ring X)))
    (ε : (PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K ≅
      (PurCompactSupport.push R (Compactification.Refinement.id c).hom).obj
        ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K))
    (hε : (PurCompactSupport.openDerivedAdjunction R c.i).homEquiv _ _ ε.hom ≫
      PurCompactSupport.refinementRestriction R (Compactification.Refinement.id c) hi K =
        (PurCompactSupport.openDerivedAdjunction R c.i).unit.app K) :
    ((PurCompactSupport.geometricPushComposition R
        (Compactification.Refinement.id c).hom c.g hg ≪≫
      eqToIso (congrArg (fun h ↦ PurCompactSupport.push R h)
        (Compactification.Refinement.id c).hom_g)).symm.app
        ((PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K)).hom ≫
      (PurCompactSupport.push R c.g).map ε.inv = 𝟙 _ := by
  let hid := coefficient_identity R c.g hg
  let e := derivedPullId R c.Z hid
  let ρ := conjugateIsoEquiv (derivedAdj R (𝟙 c.Z)) Adjunction.id e.symm
  let M := (PurCompactSupport.openExtension R c.i).mapDerivedCategory.obj K
  have hr : PurCompactSupport.refinementRestriction R
      (Compactification.Refinement.id c) hi K =
      (PurCompactSupport.pull R c.i).map (ρ.hom.app M) := by
    unfold PurCompactSupport.refinementRestriction PurCompactSupport.refinementPull
    exact restriction_identity_component (derivedAdj R (𝟙 c.Z)) e
      (PurCompactSupport.pull R c.i) (PurCompactSupport.pull R (c.i ≫ 𝟙 c.Z))
      (congrArg (fun a ↦ PurCompactSupport.pull R a) (Category.comp_id c.i))
      (PurCompactSupport.geometricPullComposition R c.i (𝟙 c.Z) hi)
      (derivedPull_right_unit_forward R c.i hi hid) M
  rw [hr] at hε
  have he : ε.hom ≫ ρ.hom.app M = 𝟙 M := by
    apply ((PurCompactSupport.openDerivedAdjunction R c.i).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    change _ = (PurCompactSupport.openDerivedAdjunction R c.i).homEquiv _ _ (𝟙 _)
    erw [Adjunction.homEquiv_id]
    exact hε
  have he' : ε.inv = ρ.hom.app M := by
    apply (cancel_epi ε.hom).mp
    rw [ε.hom_inv_id, he]
  have hn := identity_comparison_general
    (C := DerivedCategory (pbcModules Y (R.ring Y)))
    (D := DerivedCategory (pbcModules c.Z (R.ring c.Z)))
    (F := PurCompactSupport.pull R c.g)
    (F' := PurCompactSupport.pull R (𝟙 c.Z ≫ c.g))
    (L := PurCompactSupport.pull R (𝟙 c.Z))
    (congrArg (fun a ↦ PurCompactSupport.pull R a) (Category.id_comp c.g))
    (PurCompactSupport.geometricPullComposition R (𝟙 c.Z) c.g hg).hom e
    (derivedPull_left_unit_forward R c.g hg hid)
  have hq := conjugate_paste_identity_general
    (fun a : c.Z ⟶ Y ↦ PurCompactSupport.pull R a)
    (fun a ↦ PurCompactSupport.push R a) (fun a ↦ derivedAdj R a)
    (Category.id_comp c.g) (derivedAdj R (𝟙 c.Z)) e
    (PurCompactSupport.geometricPullComposition R (𝟙 c.Z) c.g hg).hom hn M
  change ((PurCompactSupport.geometricPushComposition R (𝟙 c.Z) c.g hg ≪≫
      eqToIso (congrArg (fun a ↦ PurCompactSupport.push R a)
        (Category.id_comp c.g))).inv.app M) ≫
      (PurCompactSupport.push R c.g).map ε.inv = 𝟙 _
  have hq' : (PurCompactSupport.geometricPushComposition R (𝟙 c.Z) c.g hg ≪≫
      eqToIso (congrArg (fun a ↦ PurCompactSupport.push R a)
        (Category.id_comp c.g))).hom.app M =
      (PurCompactSupport.push R c.g).map (ρ.hom.app M) := by
    dsimp only [PurCompactSupport.geometricPushComposition, Iso.trans_hom,
      NatTrans.comp_app]
    change _ = (PurCompactSupport.push R c.g).map
      (((conjugateEquiv (derivedAdj R (𝟙 c.Z)) Adjunction.id) e.inv).app M)
    simpa only [eqToIso.hom, conjugateIsoEquiv_apply_hom] using hq
  rw [he', ← hq']
  exact Iso.inv_hom_id_app _ M

end WeilConjectures.ConstructibleExceptionalCoefficients
