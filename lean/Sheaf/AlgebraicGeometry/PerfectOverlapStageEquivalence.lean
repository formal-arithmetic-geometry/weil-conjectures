/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle

/-! # Compatibility API for the canonical overlap equivalences

The constructions are supplied by the adopted source library. This module records
component equations for those constructions without redeclaring their names.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: def-pc-perfect-overlap-stage-equivalence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
-- Reuse the source library's cached canonical abelian structures.
attribute [local instance 2000] openComparisonModuleAbelian
  openComparisonOverModuleAbelian
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh
attribute [local instance] Functor.additive_of_preserves_binary_products

section
private noncomputable def sections {C : Type*} [Category* C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (U : Cᵒᵖ) :
    SheafOfModules.{v} R ⥤ Ab :=
  (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
    (evaluation Cᵒᵖ Ab).obj U

private theorem sections_map_comp {C : Type*} [Category* C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (U : Cᵒᵖ)
    {M N P : SheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) :
    (sections R U).map (f ≫ g) = (sections R U).map f ≫ (sections R U).map g := rfl

section
variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F G : C ⥤ D} [F.IsContinuous J K] [G.IsContinuous J K]
  {R : Sheaf K RingCat.{u}} {S : Sheaf J RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (U : Cᵒᵖ)

private theorem sections_pushforwardCongr
    {ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    (e : φ = ψ) (M : SheafOfModules.{v} R) :
    (sections S U).map ((SheafOfModules.pushforwardCongr e).hom.app M) = 𝟙 _ := rfl

private theorem sections_pushforwardNatTrans
    (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (a : F ⟶ G) (M : SheafOfModules.{v} R) :
    (sections S U).map ((SheafOfModules.pushforwardNatTrans ψ a).app M) =
      M.val.presheaf.map (a.app U.unop).op := rfl

variable {D' : Type*} [Category* D'] {K' : GrothendieckTopology D'}
  {H : D ⥤ D'} {R' : Sheaf K' RingCat.{u}} [H.IsContinuous K K']
  (ψ : R ⟶ (H.sheafPushforwardContinuous RingCat.{u} K K').obj R')

private theorem sections_pushforwardComp_hom (M : SheafOfModules.{v} R') :
    (sections S U).map ((SheafOfModules.pushforwardComp φ ψ).hom.app M) = 𝟙 _ := rfl

private theorem sections_pushforwardComp_inv (M : SheafOfModules.{v} R') :
    (sections S U).map ((SheafOfModules.pushforwardComp φ ψ).inv.app M) = 𝟙 _ := rfl

end

private theorem sections_iso_ext {C A : Type*} [Category* C] [Category* A]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {F G : A ⥤ SheafOfModules.{v} R} (a b : F ≅ G)
    (h : ∀ M U, (sections R U).map (a.hom.app M) =
      (sections R U).map (b.hom.app M)) : a = b := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map_injective
  apply NatTrans.ext
  funext U
  exact h M U

private theorem sections_overFunctorMap (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) (M : X.Modules) (V : W.toScheme.Opensᵒᵖ) :
    (sections W.toScheme.ringCatSheaf V).map
      ((Scheme.Modules.overEquiv W).functor.map
        ((SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app M)) = 𝟙 _ := rfl

private theorem sections_overFunctorEquiv (X : Scheme.{u})
    (U : X.Opens) (M : X.Modules) (V : U.toScheme.Opensᵒᵖ) :
    (sections U.toScheme.ringCatSheaf V).map
      ((Scheme.Modules.overFunctorEquiv U).hom.app M) = 𝟙 _ := rfl

private theorem sections_restrictFunctor_map {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules} (a : M ⟶ N)
    (V : X.Opensᵒᵖ) :
    (sections X.ringCatSheaf V).map ((Scheme.Modules.restrictFunctor f).map a) =
      (sections Y.ringCatSheaf (.op (f ''ᵁ V.unop))).map a := rfl

private theorem sections_restrictFunctorComp_inv {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Z.Modules) (V : X.Opensᵒᵖ) :
    (sections X.ringCatSheaf V).map
      ((Scheme.Modules.restrictFunctorComp f g).inv.app M) =
      M.presheaf.map (eqToHom (by simp)).op := rfl

private theorem sections_restrictFunctorCongr_hom {X Y : Scheme.{u}}
    {f g : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g)
    (M : Y.Modules) (V : X.Opensᵒᵖ) :
    (sections X.ringCatSheaf V).map
      ((Scheme.Modules.restrictFunctorCongr h).hom.app M) =
      M.presheaf.map (eqToHom (by simp [h])).op := rfl

private theorem presheaf_overFunctor_map (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) {V W : (Over U)ᵒᵖ} (a : V ⟶ W) :
    ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M).val.presheaf.map a =
      M.val.presheaf.map ((Over.forget U).map a.unop).op := rfl

attribute [local irreducible] Scheme.Hom.appIso

private theorem identityTransportCycle {C : Type*} [Category* C] {A B D : C}
    (h1 : A = B) (h2 : B = D) (h3 : D = A) :
    (𝟙 A ≫ eqToHom h1) ≫ 𝟙 B ≫ eqToHom h2 ≫ eqToHom h3 = 𝟙 A := by
  subst h1
  subst h2
  simp

private theorem overRestrictionIso_comp (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) :
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.overFunctor X.ringCatSheaf U)
        (Scheme.Modules.overMapCompOverEquiv i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U)
        (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))) ≪≫
      (Scheme.Modules.restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X (leOfHom i)) =
    Functor.isoWhiskerRight (SheafOfModules.overFunctorMap X.ringCatSheaf i)
      (Scheme.Modules.overEquiv W).functor ≪≫ Scheme.Modules.overFunctorEquiv W := by
  apply sections_iso_ext
  intro M V
  dsimp only [Scheme.Modules, Scheme.Modules.instCategory] at *
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp, Functor.map_comp, Category.comp_id,
    sections_overFunctorMap, sections_restrictFunctor_map,
    sections_overFunctorEquiv, sections_restrictFunctorComp_inv,
    sections_restrictFunctorCongr_hom]
  simp only [Scheme.Modules.overMapCompOverEquiv, SheafOfModules.pushforwardCongr₂,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    SheafOfModules.pushforwardNatIso_hom, sections_map_comp,
    sections_pushforwardComp_hom, sections_pushforwardComp_inv,
    sections_pushforwardCongr, sections_pushforwardNatTrans, presheaf_overFunctor_map,
    Category.comp_id]
  simp only [NatIso.ofComponents_hom_app, Over.forget_map, eqToHom_op, eqToHom_map]
  simp only [Quiver.Hom.unop_op, Over.isoMk_hom_left,
    eqToIso.hom, Scheme.Modules.presheaf, eqToHom_op, eqToHom_map]
  dsimp only [sections, Scheme.Modules.overEquiv, SheafOfModules.overMap,
    TopologicalSpace.Opens.sheafOfModulesEquivOver,
    SheafOfModules.pushforwardPushforwardEquivalence, Functor.comp_obj,
    SheafOfModules.pushforward, SheafOfModules.forget, PresheafOfModules.toPresheaf,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj, PresheafOfModules.presheaf,
    ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj',
    ModuleCat.hasForgetToAddCommGroup, CategoryTheory.evaluation]
  exact identityTransportCycle (C := Ab.{u}) _ _ _
end

@[simp] private theorem restrict_map_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (a : M ⟶ N) (V : X.Opens) :
    ((Scheme.Modules.restrictFunctor f).map a).app V = a.app (f ''ᵁ V) := rfl

private theorem restrictComp_mate {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((Scheme.Modules.restrictAdjunction g).comp
      (Scheme.Modules.restrictAdjunction f)) (Scheme.Modules.restrictAdjunction (f ≫ g))
      (Scheme.Modules.restrictFunctorComp f g).hom =
        (Scheme.Modules.pushforwardComp f g).hom := by
  ext M V
  have hid (a : Opposite.op (f ⁻¹ᵁ (g ⁻¹ᵁ V)) ⟶
      Opposite.op (f ⁻¹ᵁ (g ⁻¹ᵁ V))) : M.presheaf.map a = 𝟙 _ := by
    rw [Subsingleton.elim a (𝟙 _), CategoryTheory.Functor.map_id]
  simp only [Scheme.Modules.pushforward_obj_obj, Scheme.Hom.comp_base,
    TopologicalSpace.Opens.map_comp_obj, Functor.comp_obj, conjugateEquiv_apply_app,
    Adjunction.comp_counit_app, ← Functor.map_comp, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, homOfLE_leOfHom,
    Scheme.Modules.pushforward_obj_presheaf_map, TopologicalSpace.Opens.map_homOfLE,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Functor.op_obj, restrict_map_app, Scheme.Modules.restrictAdjunction_counit_app_app,
    hid, AddCommGrpCat.hom_id, AddMonoidHom.id_apply,
    Scheme.Modules.pushforwardComp_hom_app_app]

private noncomputable def tensorRestrictIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.restrictFunctor f :=
  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (Scheme.Modules.restrictAdjunction f)

private theorem tensorRestrictIso_conjugate {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.restrictAdjunction f)
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
      (tensorRestrictIso f).hom = 𝟙 (Scheme.Modules.pushforward f) := by
  simp [tensorRestrictIso, Adjunction.leftAdjointUniq]

private theorem tensorRestrictIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    tensorRestrictIso (f ≫ g) ≪≫ Scheme.Modules.restrictFunctorComp f g =
      Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl ≪≫
        Functor.isoWhiskerRight (tensorRestrictIso g) (Scheme.Modules.tensorPullback f) ≪≫
        Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor g) (tensorRestrictIso f) := by
  apply Iso.ext
  let aTf := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)
  let aTg := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let aTfg := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g))
  let aRf := Scheme.Modules.restrictAdjunction f
  let aRg := Scheme.Modules.restrictAdjunction g
  let aRfg := Scheme.Modules.restrictAdjunction (f ≫ g)
  apply (conjugateEquiv (aRg.comp aRf) aTfg).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _ aRfg,
    ← conjugateEquiv_comp _ (aTg.comp aTf),
    ← conjugateEquiv_comp _ (aRg.comp aTf)]
  rw [restrictComp_mate, tensorRestrictIso_conjugate,
    conjugateEquiv_whiskerLeft aRf aTf aRg,
    conjugateEquiv_whiskerRight aRg aTg aTf,
    tensorRestrictIso_conjugate, tensorRestrictIso_conjugate]
  have ht := congrArg Iso.hom ((conjugateIsoEquiv (aTg.comp aTf) aTfg).apply_symm_apply
    (Scheme.Modules.pushforwardComp f g ≪≫ Scheme.Modules.pushforwardCongr rfl))
  change conjugateEquiv (aTg.comp aTf) aTfg
    (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).hom = _ at ht
  rw [ht]
  have hp : (Scheme.Modules.pushforwardCongr (rfl : f ≫ g = f ≫ g)).hom =
      𝟙 _ := by
    ext M V
    simp
  simp [hp]
private theorem tensorRestrictIso_original {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback f).symm = tensorRestrictIso f := by
  apply Iso.ext
  exact Adjunction.leftAdjointUniq_trans _ _ _

private theorem tensorRestrictIso_compTo {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion k] :
    Scheme.Modules.tensorPullbackCompositionIso f g k h ≪≫
      Functor.isoWhiskerRight (tensorRestrictIso g) (Scheme.Modules.tensorPullback f) ≪≫
        Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor g) (tensorRestrictIso f) ≪≫
          (Scheme.Modules.restrictFunctorComp f g).symm ≪≫
            Scheme.Modules.restrictFunctorCongr h = tensorRestrictIso k := by
  cases h
  have he : Scheme.Modules.restrictFunctorCongr (rfl : f ≫ g = f ≫ g) =
      Iso.refl _ := by
    ext M V
    simp
    rfl
  rw [he, Iso.trans_refl]
  have ht := congrArg (fun t ↦ t ≪≫ (Scheme.Modules.restrictFunctorComp f g).symm)
    (tensorRestrictIso_comp f g)
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using ht.symm
private theorem whiskerAlgebra
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {T R P : A ⥤ B} {V S Q : B ⥤ C} {H K O : A ⥤ C}
    (a : T ≅ P) (r : R ≅ P) (b : V ≅ Q) (s : S ≅ Q)
    (c : H ≅ O) (t : K ≅ O) (d : R ⋙ S ≅ K) (e : H ≅ T ⋙ V)
    (f : P ⋙ Q ≅ O)
    (hg : Functor.isoWhiskerLeft R s ≪≫ Functor.isoWhiskerRight r Q ≪≫ f = d ≪≫ t)
    (ht : e ≪≫ Functor.isoWhiskerRight a V ≪≫ Functor.isoWhiskerLeft P b ≪≫ f = c) :
    Functor.isoWhiskerRight (a ≪≫ r.symm) V ≪≫
      Functor.isoWhiskerLeft R (b ≪≫ s.symm) ≪≫ d = e.symm ≪≫ c ≪≫ t.symm := by
  have hd : d = Functor.isoWhiskerLeft R s ≪≫
      Functor.isoWhiskerRight r Q ≪≫ f ≪≫ t.symm := by
    have h := congrArg (fun x ↦ x ≪≫ t.symm) hg
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h.symm
  rw [hd, ← ht]
  simp only [Functor.isoWhiskerRight_trans, Functor.isoWhiskerLeft_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.isoWhiskerLeft R s.symm),
    ← Functor.isoWhiskerLeft_trans]
  simp only [Iso.symm_self_id, Functor.isoWhiskerLeft_refl, Iso.refl_trans]
  rw [← Iso.trans_assoc (Functor.isoWhiskerRight r.symm V),
    ← Functor.isoWhiskerLeft_trans_isoWhiskerRight]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.isoWhiskerRight r.symm Q),
    ← Functor.isoWhiskerRight_trans]
  simp

private noncomputable def nestedRestrictionIso (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) :
    schemeOpenOverlapRestriction X i ≅
      Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i)) :=
  Functor.isoWhiskerLeft (Scheme.Modules.overEquiv U).inverse
      (Scheme.Modules.overMapCompOverEquiv i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).counitIso _ ≪≫
    Functor.leftUnitor _

private theorem nestedComparisonAlgebra {C : Type*} [Category* C]
    {A B D E F G H : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (l : A ⟶ G) (m : G ⟶ D) (n : G ⟶ H) (o : H ⟶ F)
    (h1 : a ≫ b = l ≫ m) (h2 : m ≫ c ≫ d = n ≫ o) :
    a ≫ b ≫ 𝟙 D ≫ c ≫ d = l ≫ 𝟙 G ≫ n ≫ o := by
  simp only [Category.id_comp]
  rw [← Category.assoc a b, h1, Category.assoc l m, h2]

private theorem nestedRestrictionIso_comp (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) :
    Functor.isoWhiskerLeft (schemeOpenRestriction X U) (nestedRestrictionIso X i) ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U)
        (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))) ≪≫
      (Scheme.Modules.restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X (leOfHom i)) =
    schemeOpenRestrictionCompIso X i ≪≫ Scheme.Modules.overFunctorEquiv W := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let e := Scheme.Modules.overEquiv U
  let N := (SheafOfModules.overFunctor X.ringCatSheaf U).obj M
  have hu : e.functor.map (e.unitIso.inv.app N) =
      e.counitIso.hom.app (e.functor.obj N) := by
    apply (cancel_epi (e.counitIso.inv.app (e.functor.obj N))).mp
    rw [e.counitIso_functor_comp, Iso.inv_hom_id_app]
    rfl
  have hn := (Scheme.Modules.overMapCompOverEquiv i).hom.naturality
    (e.unitIso.inv.app N)
  simp only [Functor.comp_map] at hn
  rw [hu] at hn
  have hg := congrArg (fun t ↦ t.hom.app M) (overRestrictionIso_comp X i)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.id_comp] at hg
  simp only [nestedRestrictionIso, schemeOpenRestrictionCompIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.leftUnitor_hom_app,
    Category.id_comp, Category.assoc]
  exact nestedComparisonAlgebra _ _ _ _ _ _ _ _ hn.symm hg

private noncomputable def nestedTensorOpenIso (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U) :
    (Scheme.Modules.tensorPullback (X.homOfLE (leOfHom i)) :
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ≅
      schemeOpenOverlapRestriction X i := by
  let f := X.homOfLE (leOfHom i)
  let T : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let η : T ≅ Scheme.Modules.restrictFunctor f :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback f).symm
  exact (nestedRestrictionIso X i ≪≫ η.symm).symm

private theorem isoRearrange {C : Type*} [Category* C]
    {A B D E F : C} (a : A ≅ B) (b : B ≅ D) (c : D ≅ E)
    (e : A ≅ F) (d : F ≅ E) (h : a ≪≫ b ≪≫ c = e ≪≫ d) :
    b ≪≫ c ≪≫ d.symm = a.symm ≪≫ e := by
  have hh := congrArg (fun t ↦ a.symm ≪≫ t ≪≫ d.symm) h
  simp only [Iso.trans_assoc] at hh
  rw [← Iso.trans_assoc a.symm a, Iso.symm_self_id, Iso.refl_trans,
    Iso.self_symm_id, Iso.trans_refl] at hh
  exact hh

private theorem nestedTensorCompatibility (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    Functor.isoWhiskerLeft (schemeOpenRestriction X U) (nestedTensorOpenIso X i) ≪≫
        schemeOpenRestrictionCompIso X i ≪≫ (openPinnedTensorOpenIso X W).symm =
      Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm _ ≪≫
        (Scheme.Modules.tensorPullbackCompositionIso (X.homOfLE (leOfHom i)) U.ι W.ι
          (Scheme.homOfLE_ι X (leOfHom i))).symm := by
  let j := X.homOfLE (leOfHom i)
  let e := Scheme.Modules.tensorPullbackCompositionIso j U.ι W.ι
    (Scheme.homOfLE_ι X (leOfHom i))
  have hh := whiskerAlgebra (tensorRestrictIso U.ι) (Scheme.Modules.overFunctorEquiv U)
    (tensorRestrictIso j) (nestedRestrictionIso X i)
    (tensorRestrictIso W.ι) (Scheme.Modules.overFunctorEquiv W)
    (schemeOpenRestrictionCompIso X i) e
    ((Scheme.Modules.restrictFunctorComp j U.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X (leOfHom i)))
    (nestedRestrictionIso_comp X i)
    (tensorRestrictIso_compTo j U.ι W.ι (Scheme.homOfLE_ι X (leOfHom i)))
  have hu : openPinnedTensorOpenIso X U =
      tensorRestrictIso U.ι ≪≫ (Scheme.Modules.overFunctorEquiv U).symm := by
    dsimp only [openPinnedTensorOpenIso]
    rw [← Iso.trans_assoc, tensorRestrictIso_original]
  have hw : openPinnedTensorOpenIso X W =
      tensorRestrictIso W.ι ≪≫ (Scheme.Modules.overFunctorEquiv W).symm := by
    dsimp only [openPinnedTensorOpenIso]
    rw [← Iso.trans_assoc, tensorRestrictIso_original]
  have hj : nestedTensorOpenIso X i = tensorRestrictIso j ≪≫
      (nestedRestrictionIso X i).symm := by
    dsimp only [nestedTensorOpenIso]
    rw [Iso.trans_symm, Iso.symm_symm_eq, tensorRestrictIso_original]
  rw [← hu, ← hw, ← hj] at hh
  exact isoRearrange (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U) _)
    (Functor.isoWhiskerLeft (schemeOpenRestriction X U) (nestedTensorOpenIso X i))
    (schemeOpenRestrictionCompIso X i) e.symm (openPinnedTensorOpenIso X W) hh

private noncomputable def homotopyNatIso
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategory (.up ℤ) ≅ G.mapHomotopyCategory (.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
  inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
      NatTrans.mapHomotopyCategory_id]

private theorem homotopyNestedComparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {R : C ⥤ D} {S T : D ⥤ E} {H K : C ⥤ E}
    [R.Additive] [S.Additive] [T.Additive] [H.Additive] [K.Additive]
    (e : T ≅ S) (d : R ⋙ S ≅ H) (b : H ≅ K) (a : R ⋙ T ≅ K)
    (h : Functor.isoWhiskerLeft R e ≪≫ d ≪≫ b = a)
    (P : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((R.mapHomotopyCategory (.up ℤ)).obj P) ≫
      (Functor.mapHomotopyCategoryCompIso d (.up ℤ)).hom.app P ≫
        (NatTrans.mapHomotopyCategory b.hom (.up ℤ)).app P =
      (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).hom.app P := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((R.mapHomologicalComplex (.up ℤ)).obj L)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso d (.up ℤ)).hom.app L) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app L) =
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app L)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  have hn := congrArg (fun t ↦ t.hom.app (L.X n)) h
  simp only [HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_obj_X,
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  exact hn

private theorem derivedCompositionFactor
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] [HasDerivedCategory.{w} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : F ⋙ G ≅ H) (P : HomotopyCategory C (.up ℤ)) :
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
        Functor.mapDerivedCategoryNatIso s).hom.app (DerivedCategory.Qh.{w}.obj P) ≫
      H.mapDerivedCategoryFactorsh.hom.app P =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app P) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.{w}.map
          ((Functor.mapHomotopyCategoryCompIso s (.up ℤ)).hom.app P) := by
  have ht : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P ≫
      (NatTrans.mapHomotopyCategory s.hom (.up ℤ)).app P =
      (Functor.mapHomotopyCategoryCompIso s (.up ℤ)).hom.app P := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    change (HomotopyCategory.quotient E (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) ≫
      (HomotopyCategory.quotient E (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app K) =
      (HomotopyCategory.quotient E (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso s (.up ℤ)).hom.app K)
    rw [← Functor.map_comp]
    congr 1
    ext n
    simp [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex]
  have hc := Functor.mapDerivedCategoryCompIso_fach F G P
  have hn := Functor.mapDerivedCategoryNatIso_fach s P
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hn, ← hc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← DerivedCategory.Qh.{w}.map_comp, ht]

private theorem isoHomFromInv {C : Type*} [Category* C]
    {A B D E : C} (e : A ≅ B) (v : D ≅ E)
    (c : A ⟶ D) (s : B ⟶ E) (h : e.inv ≫ c = s ≫ v.inv) :
    e.hom ≫ s = c ≫ v.hom := by
  apply (cancel_mono v.inv).mp
  simp only [Category.assoc, v.hom_inv_id, Category.comp_id]
  rw [← h]
  simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem isoCompInvCancel3 {C : Type*} [Category* C]
    {A B D E F : C} (e : E ≅ F)
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ F) (g : A ⟶ E)
    (h : a ≫ b ≫ c ≫ e.inv = g) : a ≫ b ≫ c = g ≫ e.hom := by
  apply (cancel_mono e.inv).mp
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using h

private theorem nestedTriangleAlgebra {C : Type*} [Category* C]
    {A B D E F G H I J K : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (r : D ⟶ G) (v : G ⟶ F) (f : B ⟶ H) (g : H ⟶ I) (t : I ⟶ G)
    (l : A ⟶ J) (m : J ⟶ H) (n : J ⟶ K) (o : K ⟶ I)
    (hcd : c ≫ d = r ≫ v) (hbr : b ≫ r = f ≫ g ≫ t)
    (haf : a ≫ f = l ≫ m) (hmg : m ≫ g = n ≫ o) :
    a ≫ b ≫ c ≫ d = l ≫ n ≫ o ≫ t ≫ v := by
  rw [hcd]
  rw [← Category.assoc b r, hbr]
  simp only [Category.assoc]
  rw [← Category.assoc a f, haf]
  simp only [Category.assoc]
  rw [← Category.assoc m g, hmg]
  simp only [Category.assoc]

private theorem closeTriangle {C : Type*} [Category* C]
    {A B D E F G : C} (l r : A ⟶ G) (f : A ⟶ B) (g : B ⟶ D)
    (a : D ⟶ E) (b : E ⟶ F) (c : F ⟶ G) (d : D ⟶ G)
    (hl : l = f ≫ g ≫ a ≫ b ≫ c) (ht : a ≫ b ≫ c = d)
    (hr : r = (f ≫ g) ≫ d) : l = r := by
  rw [Category.assoc] at hr
  exact hl.trans ((congrArg (fun z ↦ f ≫ g ≫ z) ht).trans hr.symm)

private theorem isoMoveTwo {C : Type*} [Category* C]
    {A B D E : C} (a : A ≅ B) (b : B ≅ E) (c : D ≅ E) (d : A ≅ D)
    (h : a ≪≫ b ≪≫ c.symm = d) : a = d ≪≫ c ≪≫ b.symm := by
  have hh := congrArg (fun t ↦ t ≪≫ c ≪≫ b.symm) h
  simp only [Iso.trans_assoc] at hh
  rw [← Iso.trans_assoc c.symm c, Iso.symm_self_id, Iso.refl_trans,
    Iso.self_symm_id, Iso.trans_refl] at hh
  exact hh

private theorem leftDerivedUnique_inv_fac
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    {W : MorphismProperty C} {Q : C ⥤ D} [Q.IsLocalization W]
    {F : C ⥤ H} (L L' : D ⥤ H) (ε : Q ⋙ L ⟶ F) (δ : Q ⋙ L' ⟶ F)
    [L.IsLeftDerivedFunctor ε W] [L'.IsLeftDerivedFunctor δ W] (P : C) :
    (Functor.leftDerivedUnique L' L ε δ W).inv.app (Q.obj P) ≫ ε.app P = δ.app P := by
  simp only [Functor.leftDerivedUnique, Functor.leftDerivedNatIso_inv,
    Functor.leftDerivedNatTrans_app, Iso.refl_inv, NatTrans.id_app, Category.comp_id]

private theorem exactDerivedComparisonCounit
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (T S : C ⥤ D) [T.Additive] [S.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh.{w} ⋙ L ⟶
      T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w})
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (e : S ≅ T) (α : L ≅ S.mapDerivedCategory)
    (hα : α = Functor.leftDerivedUnique T.mapDerivedCategory L ε
      T.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso C (.up ℤ)) ≪≫
        (Functor.mapDerivedCategoryNatIso e).symm)
    (P : HomotopyCategory C (.up ℤ)) :
    α.inv.app (DerivedCategory.Qh.{w}.obj P) ≫ ε.app P =
      S.mapDerivedCategoryFactorsh.hom.app P ≫ DerivedCategory.Qh.{w}.map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  rw [hα]
  simp only [Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv, Category.assoc]
  rw [leftDerivedUnique_inv_fac]
  exact Functor.mapDerivedCategoryNatIso_fach e P

private theorem leftDerivedIsoCoherence
    {C D₀ D₁ D₂ : Type*} [Category* C] [Category* D₀]
    [Category* D₁] [Category* D₂]
    {Q : C ⥤ D₀} {F : C ⥤ D₂} {W : MorphismProperty C} [Q.IsLocalization W]
    {R : D₀ ⥤ D₁} {S L : D₁ ⥤ D₂} {H K : D₀ ⥤ D₂} {U : D₀ ⥤ D₁}
    (ε : Q ⋙ K ⟶ F) [K.IsLeftDerivedFunctor ε W]
    (a : L ≅ S) (b : R ⋙ S ≅ H) (c : K ≅ H) (d : U ≅ R)
    (e : U ⋙ L ≅ K)
    (h : ∀ P, a.hom.app (R.obj (Q.obj P)) ≫ b.hom.app (Q.obj P) ≫
        c.inv.app (Q.obj P) ≫ ε.app P =
      L.map (d.inv.app (Q.obj P)) ≫ e.hom.app (Q.obj P) ≫ ε.app P) :
    Functor.isoWhiskerLeft R a ≪≫ (b ≪≫ c.symm) =
      Functor.isoWhiskerRight d.symm L ≪≫ e := by
  apply Iso.ext
  apply Functor.leftDerived_ext K ε W
  apply NatTrans.ext
  funext P
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc] using h P

private theorem leftDerivedTriangleCoherence
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    {q₀ : C₀ ⥤ D₀} {q₁ : C₁ ⥤ D₁} {q₂ : C₂ ⥤ D₂}
    {W : MorphismProperty C₀} [q₀.IsLocalization W]
    {R : C₀ ⥤ C₁} {S T : C₁ ⥤ C₂} {H K : C₀ ⥤ C₂}
    {r : D₀ ⥤ D₁} {s l : D₁ ⥤ D₂} {h k : D₀ ⥤ D₂} {u : D₀ ⥤ D₁}
    (ε : q₀ ⋙ k ⟶ K ⋙ q₂) [k.IsLeftDerivedFunctor ε W]
    (δ : q₁ ⋙ l ⟶ T ⋙ q₂)
    (φ : q₀ ⋙ r ≅ R ⋙ q₁) (ψ : q₁ ⋙ s ≅ S ⋙ q₂)
    (χ : q₀ ⋙ h ≅ H ⋙ q₂)
    (e : T ≅ S) (d : R ⋙ S ≅ H) (b : K ≅ H) (a : R ⋙ T ≅ K)
    (α : l ≅ s) (β : r ⋙ s ≅ h) (κ : k ≅ h) (η : u ≅ r)
    (γ : u ⋙ l ≅ k)
    (hc : ∀ P, β.hom.app (q₀.obj P) ≫ χ.hom.app P =
      s.map (φ.hom.app P) ≫ ψ.hom.app (R.obj P) ≫ q₂.map (d.hom.app P))
    (hk : ∀ P, κ.inv.app (q₀.obj P) ≫ ε.app P =
      χ.hom.app P ≫ q₂.map (b.inv.app P))
    (hl : ∀ P, α.inv.app (q₁.obj P) ≫ δ.app P =
      ψ.hom.app P ≫ q₂.map (e.inv.app P))
    (ht : ∀ P, e.hom.app (R.obj P) ≫ d.hom.app P ≫ b.inv.app P = a.hom.app P)
    (hs : ∀ P, l.map (η.inv.app (q₀.obj P)) ≫ γ.hom.app (q₀.obj P) ≫
      ε.app P ≫ q₂.map (a.inv.app P) =
      l.map (φ.hom.app P) ≫ δ.app (R.obj P)) :
    Functor.isoWhiskerLeft r α ≪≫ (β ≪≫ κ.symm) =
      Functor.isoWhiskerRight η.symm l ≪≫ γ := by
  apply leftDerivedIsoCoherence (W := W) ε α β κ η γ
  intro P
  have hn := α.hom.naturality (φ.hom.app P)
  have hi := isoHomFromInv (α.app (q₁.obj (R.obj P)))
    (q₂.mapIso (e.app (R.obj P))) _ _ (hl (R.obj P))
  dsimp only [Functor.mapIso] at hi
  have hh := congrArg q₂.map (ht P)
  simp only [Functor.map_comp] at hh
  have hf := nestedTriangleAlgebra _ _ _ _ _ _ _ _ _ _ _ _ _
    (hk P) (hc P) hn.symm hi
  have hsrc := isoCompInvCancel3 (q₂.mapIso (a.app P)) _ _ _ _ (hs P)
  simp only [Functor.mapIso_hom, Iso.app_hom] at hsrc
  exact closeTriangle _ _ _ _ _ _ _ _ hf hh hsrc

private theorem triangleRewrite {C : Type*} [Category* C]
    {A B D E F : C} (a : A ⟶ B) (b b' : B ⟶ D) (c : D ⟶ E)
    (d d' : E ⟶ F) (r : A ⟶ F) (hb : b = b') (hd : d = d')
    (h : a ≫ b ≫ c ≫ d = r) : a ≫ b' ≫ c ≫ d' = r := by
  rw [← hb, ← hd]
  exact h

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private theorem nestedDerivedCompositionFactor (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U)
    (P : HomotopyCategory (SheafOfModules.{u}
      (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (schemeDerivedOpenRestrictionCompIso X i).hom.app (DerivedCategory.Qh.{w}.obj P) ≫
      (schemeOpenRestriction X W).mapDerivedCategoryFactorsh.hom.app P =
    (schemeOpenOverlapRestriction X i).mapDerivedCategory.map
        ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (schemeOpenOverlapRestriction X i).mapDerivedCategoryFactorsh.hom.app
        (((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.{w}.map
        ((Functor.mapHomotopyCategoryCompIso (schemeOpenRestrictionCompIso X i)
          (.up ℤ)).hom.app P) := by
  exact derivedCompositionFactor (schemeOpenRestriction X U)
    (schemeOpenOverlapRestriction X i) (schemeOpenRestriction X W)
      (schemeOpenRestrictionCompIso X i) P

section
variable [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
  (Scheme.Modules.tensorPullback k).Additive]

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackObj Scheme.Modules.tensorPullbackCompositionIso
attribute [local instance 2000] schemeOpenRestriction_additive
  schemeOpenRestriction_preservesFiniteLimits schemeOpenRestriction_preservesFiniteColimits
  schemeOpenOverlapRestriction_additive schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits
set_option maxHeartbeats 400000 in
-- Comparing the selected tensor and localization data requires extra heartbeats.
private theorem nestedCounit (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (P : HomotopyCategory (SheafOfModules.{u}
      (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)) :
    (overlapOpenInclusionPullbackIso X i).inv.app (DerivedCategory.Qh.obj P) ≫
        (pinnedPullbackCounit.{u,w} (X.homOfLE (leOfHom i))).app P =
      (schemeOpenOverlapRestriction X i).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (nestedTensorOpenIso X i).inv (.up ℤ)).app P) := by
  classical
  have : PreservesFiniteLimits (schemeOpenOverlapRestriction X i) :=
    schemeOpenOverlapRestriction_preservesFiniteLimits X i
  have : PreservesFiniteColimits (schemeOpenOverlapRestriction X i) :=
    schemeOpenOverlapRestriction_preservesFiniteColimits X i
  let f := X.homOfLE (leOfHom i)
  let T : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let e : schemeOpenOverlapRestriction X i ≅ T := (nestedTensorOpenIso X i).symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso e
  have hL := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u,w}))) f
  have := hL
  have hα : overlapOpenInclusionPullbackIso X i =
      Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback f)
        (pinnedPullbackCounit.{u,w} f) T.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)) ≪≫
        (Functor.mapDerivedCategoryNatIso e).symm := by
    rfl
  exact exactDerivedComparisonCounit T (schemeOpenOverlapRestriction X i)
    (derivedPullback f) (pinnedPullbackCounit.{u,w} f) e
    (overlapOpenInclusionPullbackIso X i) hα P

attribute [local irreducible] nestedRestrictionIso nestedTensorOpenIso
  overlapOpenInclusionPullbackIso perfectHomComposition
  singleComplexOpenPullbackIso openPinnedTensorOpenIso
attribute [local instance 2000] schemeOpenRestriction_additive
  schemeOpenRestriction_preservesFiniteLimits schemeOpenRestriction_preservesFiniteColimits
  schemeOpenOverlapRestriction_additive schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits
private theorem pinnedComposition_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pinnedPullbackComposition.{u,w} f g = perfectHomComposition f g := by
  unfold perfectHomComposition
  rfl

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem sourceHomotopyComparison_def
    {X : Scheme.{u}} (U : X.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme) :
    (openPinnedHomotopySourceCompositionIso U j).hom =
      (Functor.mapHomotopyCategoryCompIso
        (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm
          (Scheme.Modules.tensorPullback j :
            SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
              SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ≪≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).symm)
        (.up ℤ)).inv := rfl

private theorem nestedSourceTriangle
    (X : Scheme.{u}) (U : X.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme)
    (k : Y ⟶ X) (h : j ≫ U.ι = k)
    (P : HomotopyCategory (SheafOfModules.{u}
      (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app
        (DerivedCategory.Qh.{w}.obj P)) ≫
      (perfectHomComposition j U.ι ≪≫ eqToIso
        (congrArg (fun l ↦ derivedPullback.{u,w} l) h)).hom.app
          (DerivedCategory.Qh.{w}.obj P) ≫
      (pinnedPullbackCounit.{u,w} k).app P ≫
      (DerivedCategory.Qh.{w}
        (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).map
        ((Functor.mapHomotopyCategoryCompIso
        (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm
          (Scheme.Modules.tensorPullback j :
            SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
              SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ≪≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι k h).symm)
        (.up ℤ)).inv.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (pinnedPullbackCounit.{u,w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P) := by
  cases h
  simp only [eqToIso_refl, Iso.trans_refl]
  have hc := open_pinned_source_counit_triangle U j P
  have hcomp := congrArg (fun e ↦ e.hom.app (DerivedCategory.Qh.{w}.obj P))
    (pinnedComposition_eq j U.ι)
  have hmap := congrArg (fun t ↦ (DerivedCategory.Qh.{w}
    (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).map (t.app P))
    (sourceHomotopyComparison_def U j)
  exact triangleRewrite _ _ _ _ _ _ _ hcomp hmap hc

private theorem nestedDerivedCompatibility (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (ht : Functor.isoWhiskerLeft (schemeOpenRestriction X U) (nestedTensorOpenIso X i) ≪≫
        schemeOpenRestrictionCompIso X i ≪≫ (openPinnedTensorOpenIso X W).symm =
      Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm _ ≪≫
        (Scheme.Modules.tensorPullbackCompositionIso (X.homOfLE (leOfHom i)) U.ι W.ι
          (Scheme.homOfLE_ι X (leOfHom i))).symm) :
    Functor.isoWhiskerLeft (schemeOpenRestriction X U).mapDerivedCategory
        (overlapOpenInclusionPullbackIso X i) ≪≫
      schemeDerivedOpenRestrictionCompIso X i ≪≫
        (singleComplexOpenPullbackIso X W).symm =
    Functor.isoWhiskerRight (singleComplexOpenPullbackIso X U).symm _ ≪≫
      perfectHomComposition (X.homOfLE (leOfHom i)) U.ι ≪≫
        eqToIso (congrArg (fun k ↦ derivedPullback.{u,w} k)
          (Scheme.homOfLE_ι X (leOfHom i))) := by
  classical
  let j := X.homOfLE (leOfHom i)
  have : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
  have : (schemeOpenRestriction X W).Additive := schemeOpenRestriction_additive X W
  have : (schemeOpenOverlapRestriction X i).Additive :=
    schemeOpenOverlapRestriction_additive X i
  have hL := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u,w}))) W.ι
  have := hL
  exact leftDerivedTriangleCoherence
    (W := HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
    (pinnedPullbackCounit W.ι) (pinnedPullbackCounit j)
    (schemeOpenRestriction X U).mapDerivedCategoryFactorsh
    (schemeOpenOverlapRestriction X i).mapDerivedCategoryFactorsh
    (schemeOpenRestriction X W).mapDerivedCategoryFactorsh
    (homotopyNatIso (nestedTensorOpenIso X i))
    (Functor.mapHomotopyCategoryCompIso (schemeOpenRestrictionCompIso X i) (.up ℤ))
    (homotopyNatIso (openPinnedTensorOpenIso X W))
    (Functor.mapHomotopyCategoryCompIso
      (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm _ ≪≫
        (Scheme.Modules.tensorPullbackCompositionIso j U.ι W.ι
          (Scheme.homOfLE_ι X (leOfHom i))).symm) (.up ℤ))
    (overlapOpenInclusionPullbackIso X i) (schemeDerivedOpenRestrictionCompIso X i)
    (singleComplexOpenPullbackIso X W) (singleComplexOpenPullbackIso X U)
    (perfectHomComposition j U.ι ≪≫ eqToIso
      (congrArg (fun k ↦ derivedPullback.{u,w} k) (Scheme.homOfLE_ι X (leOfHom i))))
    (nestedDerivedCompositionFactor X i) (openCounit X W) (nestedCounit X i)
    (homotopyNestedComparison (nestedTensorOpenIso X i)
      (schemeOpenRestrictionCompIso X i) (openPinnedTensorOpenIso X W).symm _ ht)
    (nestedSourceTriangle X U j W.ι (Scheme.homOfLE_ι X (leOfHom i)))

end

-- Keep the canonical isomorphisms abstract while checking their public equations.
attribute [local irreducible] overlapOpenInclusionPullbackIso
  singleComplexOpenPullbackIso openPinnedTensorOpenIso perfectHomComposition
  schemeDerivedOpenRestrictionCompIso

/-- The chosen inclusion comparison is pinned to the exact nested-open
restriction after precomposition with global restriction. -/
theorem overlapOpenInclusionPullbackIso_whiskerLeft
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    let h := X.homOfLE (leOfHom i)
    Functor.isoWhiskerLeft R (overlapOpenInclusionPullbackIso X i) =
      Functor.isoWhiskerRight (singleComplexOpenPullbackIso X U).symm
          (derivedPullback h) ≪≫
        perfectHomComposition h U.ι ≪≫
          eqToIso (congrArg (fun k : W.toScheme ⟶ X ↦ derivedPullback.{u,w} k)
            (show h ≫ U.ι = W.ι from Scheme.homOfLE_ι X (leOfHom i))) ≪≫
            singleComplexOpenPullbackIso X W ≪≫
              (schemeDerivedOpenRestrictionCompIso X i).symm := by
  intro R h
  classical
  have : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
    fun {_ _} k ↦ (Classical.choose exists_derivedPullbackComposition.{u,w}) k
  have hc := nestedDerivedCompatibility X i (nestedTensorCompatibility X i)
  simpa only [Iso.trans_assoc] using isoMoveTwo _ _ _ _ hc

/-- Component form of the pinned nested-open comparison. The exact restriction
isomorphism cancels the inverse factor in the pinned comparison equation. -/
theorem overlapOpenInclusionPullbackIso_hom_comp
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : schemeDerivedCategory X) :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    let h := X.homOfLE (leOfHom i)
    ((overlapOpenInclusionPullbackIso X i).hom.app (R.obj M)) ≫
      (schemeDerivedOpenRestrictionCompIso X i).hom.app M =
      (derivedPullback h).map ((singleComplexOpenPullbackIso X U).inv.app M) ≫
        (perfectHomComposition h U.ι).hom.app M ≫
          (eqToIso (congrArg (fun k : W.toScheme ⟶ X ↦ derivedPullback.{u,w} k)
            (show h ≫ U.ι = W.ι from Scheme.homOfLE_ι X (leOfHom i)))).hom.app M ≫
            (singleComplexOpenPullbackIso X W).hom.app M := by
  intro R h
  have H := congrArg (fun e ↦ e.hom.app M)
    (overlapOpenInclusionPullbackIso_whiskerLeft X i)
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom] at H
  rw [H]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [h]

/-- Inverse component equation, arranged to cancel the exact restriction
comparison before the open-inclusion pullback comparison. -/
theorem overlapOpenInclusionPullbackIso_inv_comp
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : schemeDerivedCategory X) :
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    let h := X.homOfLE (leOfHom i)
    (schemeDerivedOpenRestrictionCompIso X i).inv.app M ≫
        (overlapOpenInclusionPullbackIso X i).inv.app (R.obj M) =
      (singleComplexOpenPullbackIso X W).inv.app M ≫
        (eqToIso (congrArg (fun k : W.toScheme ⟶ X ↦ derivedPullback.{u,w} k)
          (show h ≫ U.ι = W.ι from Scheme.homOfLE_ι X (leOfHom i)))).inv.app M ≫
          (perfectHomComposition h U.ι).inv.app M ≫
            (derivedPullback h).map ((singleComplexOpenPullbackIso X U).hom.app M) := by
  intro R h
  have H := congrArg (fun e ↦ e.inv.app M)
    (overlapOpenInclusionPullbackIso_whiskerLeft X i)
  simp only [Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Iso.symm_inv] at H
  rw [H]
  simp only [Category.assoc]
  rw [← Category.assoc ((schemeDerivedOpenRestrictionCompIso X i).inv.app M)
    ((schemeDerivedOpenRestrictionCompIso X i).hom.app M),
    Iso.inv_hom_id_app, Category.id_comp]

private theorem overlapComposition_assoc {W X Y Z : Scheme.{u}}
    (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (perfectHomComposition f g) (derivedPullback h) ≪≫
      perfectHomComposition h (f ≫ g) =
      Functor.associator (derivedPullback g) (derivedPullback f) (derivedPullback h) ≪≫
        Functor.isoWhiskerLeft (derivedPullback g) (perfectHomComposition h f) ≪≫
          perfectHomComposition (h ≫ f) g ≪≫
          eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k) (Category.assoc h f g)) := by
  unfold perfectHomComposition
  exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))).2).2.2 h f g

/-- Component equation for the pinned stage comparison, with the cartesian
factor associated in the order used by the pullback prism. -/
theorem perfectOverlapStageObjectIso_hom_app
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (p' : X ⟶ T) (p : Y ⟶ S)
    (q : T ⟶ S) (h : IsPullback g p' p q)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (A : schemeDerivedCategory L.toScheme) :
    let hW' : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ L := fun _ hx ↦ hWL hx
    let e := ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback
    let fac : e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
        pullback.fst ((U ⊓ V).ι ≫ p) q ≫ Y.homOfLE hWL := by
      have restricted : X.homOfLE hW' ≫ (g ∣_ L) =
          (g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL := by
        apply (cancel_mono L.ι).1
        simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
        rw [← Category.assoc, Scheme.homOfLE_ι]
        rfl
      calc
        e.inv ≫ (X.homOfLE hW' ≫ (g ∣_ L)) =
            e.inv ≫ ((g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL) := by rw [restricted]
        _ = (e.inv ≫ (g ∣_ (U ⊓ V))) ≫ Y.homOfLE hWL := by
              simp only [Category.assoc]
        _ = _ := by rw [((isPullback_morphismRestrict g (U ⊓ V)).paste_vert h).isoPullback_inv_fst]
    ((perfectOverlapStageObjectIso g p' p q h U V L hWL).app A).hom =
      ((Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (derivedPullback (g ∣_ L))
            (overlapOpenInclusionPullbackIso X (homOfLE hW')).symm ≪≫
            perfectHomComposition (X.homOfLE hW') (g ∣_ L))
          (derivedPullback e.inv) ≪≫
        perfectHomComposition e.inv (X.homOfLE hW' ≫ (g ∣_ L)) ≪≫
        eqToIso (congrArg (fun f ↦ derivedPullback f) fac) ≪≫
        (perfectHomComposition (pullback.fst ((U ⊓ V).ι ≫ p) q)
          (Y.homOfLE hWL)).symm).app A).hom := by
  intro hW' e fac
  have hc := congrArg (fun t ↦ NatTrans.app t A)
    (congrArg Iso.hom (overlapComposition_assoc e.inv (X.homOfLE hW') (g ∣_ L)))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hc
  dsimp only [perfectOverlapStageObjectIso]
  simp only [id, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
    Category.assoc, Functor.map_comp]
  rw [reassoc_of% hc]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]
  rfl

end AlgebraicGeometry
