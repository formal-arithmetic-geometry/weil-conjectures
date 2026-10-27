/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Bidual evaluation under reindexing

Source: Stacks Project, Tag 04TT, localized internal Hom and evaluation;
WeilConjectures/WeilSheaf/Dual.lean, `dualStr` and `dual`, generalized to ringed sites
(blueprint: lem-sf-reindexed-sheaf-bidual-equivariance).

The comparison and the two contragredient structures are specified on every slice.
Existential quantification supplies these uniquely specified isomorphisms without
choosing an object from a postponed existence proof.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false in
private theorem reindexHom_bijective
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.IsEquivalence] (R : Dᵒᵖ ⥤ RingCat.{u})
    {S : Cᵒᵖ ⥤ RingCat.{u}} (t : S ≅ F.op ⋙ R)
    (M N : PresheafOfModules.{u} R) :
    Function.Bijective (fun f : M ⟶ N ↦ (PresheafOfModules.pushforward t.hom).map f) := by
  let W := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj F.op
  have hi : Function.Injective (fun f : M ⟶ N ↦
      (PresheafOfModules.pushforward t.hom).map f) := by
    intro f g h
    apply (PresheafOfModules.toPresheaf R).map_injective
    apply W.map_injective
    exact congrArg ((PresheafOfModules.toPresheaf S).map) h
  refine ⟨hi, ?_⟩
  intro α
  let β : M.presheaf ⟶ N.presheaf :=
    W.preimage ((PresheafOfModules.toPresheaf S).map α)
  have hb (X : Cᵒᵖ) (x : M.obj (F.op.obj X)) :
      β.app (F.op.obj X) x = α.app X x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (W.map_preimage (X := M.presheaf) (Y := N.presheaf)
        ((PresheafOfModules.toPresheaf S).map α)) X) x
  have hs (Y : Dᵒᵖ) (r : R.obj Y) (x : M.obj Y) :
      β.app Y (r • x) = r • β.app Y x := by
    let e := F.op.objObjPreimageIso Y
    apply (ConcreteCategory.bijective_of_isIso (N.presheaf.map e.inv)).1
    change N.map e.inv (β.app Y (r • x)) = N.map e.inv (r • β.app Y x)
    have hn (z : M.obj Y) :
        N.map e.inv (β.app Y z) = β.app _ (M.map e.inv z) :=
      (β.naturality_apply e.inv z).symm
    rw [hn, M.map_smul, hb, N.map_smul, hn, hb]
    obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso
      (t.hom.app (F.op.objPreimage Y))).2 (R.map e.inv r)
    rw [← hq]
    exact (α.app _).hom.map_smul q _
  refine ⟨PresheafOfModules.homMk β hs, ?_⟩
  ext X x
  exact hb X x

private theorem sectionwise_isIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [∀ X, IsIso (f.val.app X)] : IsIso f := by
  let e := PresheafOfModules.isoMk (fun X ↦ asIso (f.val.app X))
    (fun _ _ g ↦ f.val.naturality g)
  have he : e.hom = f.val := rfl
  have hi : IsIso f.val := by rw [← he]; infer_instance
  exact @isIso_of_reflects_iso _ _ _ _ _ _ f (SheafOfModules.forget _) hi inferInstance

@[irreducible] private noncomputable def mappedIso
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) {X Y : A} (e : X ≅ Y) :
    F.obj X ≅ F.obj Y := F.mapIso e

private theorem mappedIso_hom
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) {X Y : A} (e : X ≅ Y) :
    (mappedIso F e).hom = F.map e.hom := by
  unfold mappedIso
  rfl

private theorem fixedPair_inverse
    {A : Type*} [Category A] (T : A ⥤ A) {M N : A}
    (a : T.obj M ≅ M) (c : T.obj N ≅ N) (f : M ⟶ N)
    (h : T.map f ≫ c.hom = a.hom ≫ f) :
    (∃ d : Endofunctor.IsoAlgebra.mk M a ⟶ Endofunctor.IsoAlgebra.mk N c,
      (Endofunctor.IsoAlgebra.forget T).map d = f) ∧
    (∀ [IsIso f], T.map (inv f) ≫ a.hom = c.hom ≫ inv f ∧
      ∃ e : Endofunctor.IsoAlgebra.mk M a ≅ Endofunctor.IsoAlgebra.mk N c,
        (Endofunctor.IsoAlgebra.forget T).map e.hom = f ∧
        (Endofunctor.IsoAlgebra.forget T).map e.inv = inv f) := by
  constructor
  · exact ⟨ObjectProperty.homMk ⟨f, h⟩, rfl⟩
  · intro hi
    have hinv : T.map (inv f) ≫ a.hom = c.hom ≫ inv f := by
      apply (cancel_mono f).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← h, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    refine ⟨hinv, ?_⟩
    let e : Endofunctor.IsoAlgebra.mk M a ≅ Endofunctor.IsoAlgebra.mk N c :=
      { hom := ObjectProperty.homMk ⟨f, h⟩
        inv := ObjectProperty.homMk ⟨inv f, hinv⟩
        hom_inv_id := by
          apply ObjectProperty.hom_ext
          apply Endofunctor.Algebra.Hom.ext
          change f ≫ inv f = 𝟙 _
          exact IsIso.hom_inv_id f
        inv_hom_id := by
          apply ObjectProperty.hom_ext
          apply Endofunctor.Algebra.Hom.ext
          change inv f ≫ f = 𝟙 _
          exact IsIso.inv_hom_id f }
    exact ⟨e, rfl, rfl⟩

section Reindex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (τ : C ≌ C) [τ.functor.IsContinuous J J]
  (R : Sheaf J CommRingCat.{u})
  (s : (τ.functor.sheafPushforwardContinuous RingCat.{u} J J).obj
    ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) ≅
    (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def reindexUnitIso :
    (pushforward (F := τ.functor) s.inv).obj (unit _) ≅ unit _ where
  hom.val.app X := by
    let σ : R.obj.obj (op (τ.functor.obj X.unop)) →+* R.obj.obj X :=
      (s.hom.hom.app X).hom
    let t : R.obj.obj X →+* R.obj.obj (op (τ.functor.obj X.unop)) :=
      (s.inv.hom.app X).hom
    exact ModuleCat.ofHom
      (X := ((pushforward (F := τ.functor) s.inv).obj (unit _)).val.obj X)
      (Y := (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj X)
      { toFun := σ
        map_add' := map_add _
        map_smul' r x := by
          change R.obj.obj X at r
          change R.obj.obj (op (τ.functor.obj X.unop)) at x
          change σ (t r * x) = r * σ x
          rw [map_mul]
          have h := ConcreteCategory.congr_hom (NatTrans.congr_app
            (congrArg (fun f : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
              (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ↦ f.hom) s.inv_hom_id) X) r
          change σ (t r) = r at h
          rw [h] }
  hom.val.naturality f := by
    ext x
    exact ConcreteCategory.congr_hom (s.hom.hom.naturality f) x
  inv.val.app X := ModuleCat.ofHom
    (X := (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj X)
    (Y := ((pushforward (F := τ.functor) s.inv).obj (unit _)).val.obj X)
    { toFun := s.inv.hom.app X
      map_add' := map_add _
      map_smul' r x := by
        change R.obj.obj X at r x
        change s.inv.hom.app X (r * (x : R.obj.obj X)) = _
        exact map_mul _ r x }
  inv.val.naturality f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (s.inv.hom.naturality f) x
  hom_inv_id := by
    ext X x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f ↦ f.hom) s.hom_inv_id) X) x
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
              (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ↦ f.hom) s.inv_hom_id) X) x

private theorem reindexUnitIso_apply (X : Cᵒᵖ)
    (x : R.obj.obj (op (τ.functor.obj X.unop))) :
    (reindexUnitIso τ R s).hom.val.app X x = s.hom.hom.app X x := by
  unfold reindexUnitIso
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def reindexDualSection
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (X : Cᵒᵖ) (μ : (homObj (R := R) M (unit _)).val.obj (op (τ.functor.obj X.unop))) :
    (homObj (R := R) ((pushforward (F := τ.functor) s.inv).obj M) (unit _)).val.obj X :=
  { app W := ModuleCat.ofHom
      (X := ((pushforward (F := τ.functor) s.inv).obj M).val.obj (op W.unop.left))
      (Y := (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val.obj
        (op W.unop.left))
      { toFun := fun x ↦ s.hom.hom.app (op W.unop.left)
          (μ.app (op (Over.mk (τ.functor.map W.unop.hom))) x)
        map_add' := by intros; simp only [map_add]; rfl
        map_smul' r x := by
          change R.obj.obj (op W.unop.left) at r
          change M.val.obj (op (τ.functor.obj W.unop.left)) at x
          let σ : R.obj.obj (op (τ.functor.obj W.unop.left)) →+*
              R.obj.obj (op W.unop.left) := (s.hom.hom.app (op W.unop.left)).hom
          let t : R.obj.obj (op W.unop.left) →+*
              R.obj.obj (op (τ.functor.obj W.unop.left)) :=
            (s.inv.hom.app (op W.unop.left)).hom
          let m : M.val.obj (op (τ.functor.obj W.unop.left)) →ₗ[
              R.obj.obj (op (τ.functor.obj W.unop.left))]
              R.obj.obj (op (τ.functor.obj W.unop.left)) :=
            (μ.app (op (Over.mk (τ.functor.map W.unop.hom)))).hom
          change σ (m (t r • x)) = r * σ (m x)
          rw [map_smul, smul_eq_mul, map_mul]
          have h := ConcreteCategory.congr_hom (NatTrans.congr_app
            (congrArg (fun f : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
              (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ↦ f.hom)
              s.inv_hom_id) (op W.unop.left)) r
          change σ (t r) = r at h
          rw [h] }
    naturality {W W'} f := by
      ext x
      change s.hom.hom.app (op W'.unop.left) (μ.app
        (op (Over.mk (τ.functor.map W'.unop.hom)))
        (M.val.map (τ.functor.map f.unop.left).op x)) =
        R.obj.map f.unop.left.op (s.hom.hom.app (op W.unop.left)
          (μ.app (op (Over.mk (τ.functor.map W.unop.hom))) x))
      have hn := PresheafOfModules.naturality_apply μ
        ((Over.post τ.functor).map f.unop).op x
      have hs := ConcreteCategory.congr_hom
        (s.hom.hom.naturality f.unop.left.op)
        (μ.app (op (Over.mk (τ.functor.map W.unop.hom))) x)
      exact (congrArg (s.hom.hom.app (op W'.unop.left)) hn).trans hs }

private theorem reindexDualSection_apply
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (X : Cᵒᵖ) (μ : (homObj (R := R) M (unit _)).val.obj (op (τ.functor.obj X.unop)))
    (W : (Over X.unop)ᵒᵖ)
    (x : M.val.obj (op (τ.functor.obj W.unop.left))) :
    (reindexDualSection τ R s M X μ).app W x =
      s.hom.hom.app (op W.unop.left)
        (μ.app (op (Over.mk (τ.functor.map W.unop.hom))) x) := by
  unfold reindexDualSection
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem reindexDualSection_add
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (X : Cᵒᵖ)
    (μ ν : ((pushforward (F := τ.functor) s.inv).obj
      (homObj (R := R) M (unit _))).val.obj X) :
    reindexDualSection τ R s M X (μ + ν) =
      reindexDualSection τ R s M X μ + reindexDualSection τ R s M X ν := by
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  change (reindexDualSection τ R s M X (μ + ν)).app W x =
    (reindexDualSection τ R s M X μ).app W x +
      (reindexDualSection τ R s M X ν).app W x
  simp only [reindexDualSection_apply]
  change s.hom.hom.app (op W.unop.left)
    (μ.app (op (Over.mk (τ.functor.map W.unop.hom))) x +
      ν.app (op (Over.mk (τ.functor.map W.unop.hom))) x) = _
  exact map_add _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem reindexDualSection_smul
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (X : Cᵒᵖ) (r : R.obj.obj X)
    (μ : ((pushforward (F := τ.functor) s.inv).obj
      (homObj (R := R) M (unit _))).val.obj X) :
    reindexDualSection τ R s M X (r • μ) = r • reindexDualSection τ R s M X μ := by
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  change (reindexDualSection τ R s M X (r • μ)).app W x =
    (r • reindexDualSection τ R s M X μ).app W x
  simp only [reindexDualSection_apply]
  let σ : R.obj.obj (op (τ.functor.obj W.unop.left)) →+*
      R.obj.obj (op W.unop.left) := (s.hom.hom.app (op W.unop.left)).hom
  let t : R.obj.obj X →+* R.obj.obj (op (τ.functor.obj X.unop)) :=
    (s.inv.hom.app X).hom
  let m : R.obj.obj (op (τ.functor.obj W.unop.left)) :=
    μ.app (op (Over.mk (τ.functor.map W.unop.hom))) x
  have he := reindexDualSection_apply τ R s M X μ W x
  change (reindexDualSection τ R s M X μ).app W x = σ m at he
  change σ (R.obj.map (τ.functor.map W.unop.hom).op (t r) * m) =
    R.obj.map W.unop.hom.op r • (reindexDualSection τ R s M X μ).app W x
  rw [he]
  change σ (R.obj.map (τ.functor.map W.unop.hom).op (t r) * m) =
    R.obj.map W.unop.hom.op r * σ m
  rw [map_mul]
  congr 1
  have hs := ConcreteCategory.congr_hom (s.hom.hom.naturality W.unop.hom.op)
    (s.inv.hom.app X r)
  have hi := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
        (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ↦ f.hom) s.inv_hom_id) X) r
  exact hs.trans (congrArg (R.obj.map W.unop.hom.op) hi)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def reindexDualLinear
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (X : Cᵒᵖ) :
    ((pushforward (F := τ.functor) s.inv).obj (homObj (R := R) M (unit _))).val.obj X ⟶
      (homObj (R := R) ((pushforward (F := τ.functor) s.inv).obj M) (unit _)).val.obj X :=
  ModuleCat.ofHom
    (X := ((pushforward (F := τ.functor) s.inv).obj
      (homObj (R := R) M (unit _))).val.obj X)
    (Y := (homObj (R := R) ((pushforward (F := τ.functor) s.inv).obj M)
      (unit _)).val.obj X)
    { toFun := reindexDualSection τ R s M X
      map_add' := reindexDualSection_add τ R s M X
      map_smul' := reindexDualSection_smul τ R s M X }

private theorem reindexDualLinear_apply
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (X : Cᵒᵖ) (μ : (homObj (R := R) M (unit _)).val.obj (op (τ.functor.obj X.unop))) :
    reindexDualLinear τ R s M X μ = reindexDualSection τ R s M X μ := by
  unfold reindexDualLinear
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def reindexDualMap
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (pushforward (F := τ.functor) s.inv).obj (homObj (R := R) M (unit _)) ⟶
      homObj (R := R) ((pushforward (F := τ.functor) s.inv).obj M) (unit _) where
  val.app X := reindexDualLinear τ R s M X
  val.naturality f := by
    ext μ : 2
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    change (reindexDualLinear τ R s M _
      (PresheafOfModules.restrictOverMap (τ.functor.map f.unop) μ)).app W x =
        (PresheafOfModules.restrictOverMap f.unop (reindexDualLinear τ R s M _ μ)).app W x
    rw [reindexDualLinear_apply, reindexDualLinear_apply]
    change (reindexDualSection τ R s M _
      (PresheafOfModules.restrictOverMap (τ.functor.map f.unop) μ)).app W x =
        (reindexDualSection τ R s M _ μ).app
          (op ((Over.map f.unop).obj W.unop)) x
    rw [reindexDualSection_apply, reindexDualSection_apply]
    change s.hom.hom.app (op W.unop.left) (μ.app
      (op (Over.mk (τ.functor.map W.unop.hom ≫ τ.functor.map f.unop))) x) =
      s.hom.hom.app (op W.unop.left)
        (μ.app (op (Over.mk (τ.functor.map (W.unop.hom ≫ f.unop)))) x)
    congr 1
    exact PresheafOfModules.restrictOver_hom_app_congr μ (τ.functor.map_comp _ _).symm x

private theorem reindexDualMap_apply
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (X : Cᵒᵖ) (μ : (homObj (R := R) M (unit _)).val.obj (op (τ.functor.obj X.unop))) :
    (reindexDualMap τ R s M).val.app X μ = reindexDualSection τ R s M X μ := by
  unfold reindexDualMap
  exact reindexDualLinear_apply τ R s M X μ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reindexDualMap_bijective
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (X : Cᵒᵖ) : Function.Bijective ((reindexDualMap τ R s M).val.app X) := by
  let F := Over.post (X := X.unop) τ.functor
  let t : (Over.forget X.unop).op ⋙ R.obj ⋙ forget₂ CommRingCat RingCat ≅
      F.op ⋙ (Over.forget (τ.functor.obj X.unop)).op ⋙ R.obj ⋙
        forget₂ CommRingCat RingCat :=
    Functor.isoWhiskerLeft (Over.forget X.unop).op
      ((sheafToPresheaf J RingCat).mapIso s.symm)
  let P := (PresheafOfModules.restrictOver R.obj (τ.functor.obj X.unop)).obj M.val
  let Q := (PresheafOfModules.restrictOver R.obj (τ.functor.obj X.unop)).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).val
  have h := reindexHom_bijective F _ t P Q
  let e := (PresheafOfModules.restrictOver R.obj X.unop).mapIso
    ((SheafOfModules.forget _).mapIso (reindexUnitIso τ R s))
  have he : Function.Bijective (fun f :
      (PresheafOfModules.pushforward t.hom).obj P ⟶
        (PresheafOfModules.pushforward t.hom).obj Q ↦ f ≫ e.hom) := by
    exact ⟨fun f g h ↦ (cancel_mono e.hom).1 h,
      fun g ↦ ⟨g ≫ e.inv, by simp⟩⟩
  have hf : (fun μ ↦ (reindexDualMap τ R s M).val.app X μ) =
      (fun μ ↦ (PresheafOfModules.pushforward t.hom).map μ ≫ e.hom) := by
    funext μ
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    rw [reindexDualMap_apply, reindexDualSection_apply]
    exact (reindexUnitIso_apply τ R s (op W.unop.left) _).symm
  change Function.Bijective (fun μ ↦ (reindexDualMap τ R s M).val.app X μ)
  rw [hf]
  exact he.comp h

set_option backward.isDefEq.respectTransparency false in
private theorem reindexDualMap_isIso
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    IsIso (reindexDualMap τ R s M) := by
  let q := reindexDualMap τ R s M
  have hi (X : Cᵒᵖ) : IsIso (q.val.app X) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact reindexDualMap_bijective τ R s M X
  exact @sectionwise_isIso _ _ _ _ _ _ q hi

private noncomputable def reindexDualIso
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (pushforward (F := τ.functor) s.inv).obj (homObj (R := R) M (unit _)) ≅
      homObj (R := R) ((pushforward (F := τ.functor) s.inv).obj M) (unit _) :=
  have := reindexDualMap_isIso τ R s M
  asIso (reindexDualMap τ R s M)

private theorem reindexDualIso_hom
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (reindexDualIso τ R s M).hom = reindexDualMap τ R s M := rfl

@[irreducible] private noncomputable def dualIso
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (e : M ≅ N) : homObj (R := R) N (unit _) ≅ homObj (R := R) M (unit _) :=
  mappedIso ((homFunctor R).flip.obj (unit _)) e.op

private theorem dualIso_hom
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (e : M ≅ N) : (dualIso R e).hom = homObjMap (R := R) e.hom (𝟙 _) := by
  unfold dualIso
  rw [mappedIso_hom]
  rfl

@[irreducible] private noncomputable def contragredient
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (a : (pushforward (F := τ.functor) s.inv).obj M ≅ M) :
    (pushforward (F := τ.functor) s.inv).obj (homObj (R := R) M (unit _)) ≅
      homObj (R := R) M (unit _) :=
  reindexDualIso τ R s M ≪≫ dualIso R a.symm

private theorem contragredient_apply
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (a : (pushforward (F := τ.functor) s.inv).obj M ≅ M)
    (U V : C) (f : V ⟶ U)
    (μ : (homObj (R := R) M (unit _)).val.obj (op (τ.functor.obj U)))
    (x : M.val.obj (op V)) :
    (((contragredient τ R s M a).hom.val.app (op U) μ).app (op (Over.mk f))) x =
      s.hom.hom.app (op V)
        ((μ.app (op (Over.mk (τ.functor.map f)))) (a.inv.val.app (op V) x)) := by
  unfold contragredient
  change ((((reindexDualIso τ R s M).hom ≫ (dualIso R a.symm).hom).val.app
    (op U) μ).app (op (Over.mk f))) x = _
  rw [reindexDualIso_hom, dualIso_hom]
  change ((reindexDualMap τ R s M).val.app (op U) μ).app (op (Over.mk f))
    (a.inv.val.app (op V) x) = _
  rw [reindexDualMap_apply]
  exact reindexDualSection_apply τ R s M (op U) μ (op (Over.mk f)) _

end Reindex

/-- Bidual evaluation intertwines reindexing and the twice-induced contragredient action.

Source: Stacks Project, Tag 04TT; WeilConjectures/WeilSheaf/Dual.lean, `dualStr`,
with the direct ringed-site calculation
(blueprint: lem-sf-reindexed-sheaf-bidual-equivariance).

Proof: (1) Reindex a localized linear map along the equivalence C/U -> C/(tau U).
Its components are the original components at tau(V -> U); inverse translation
recovers the map. Transporting the target ring by s gives the comparison below.
(2) Ordinary bidual evaluation sends x to the local map lambda -> lambda(x).
Reindexing gives precisely that same formula on translated slices.
(3) Define b(mu) = s mu a^{-1}, whose inverse is lambda -> s^{-1} lambda a.
Semilinearity of a makes these maps linear for the transported R-action, and
naturality makes them commute with restriction. Repeat with (D(M),b) to get c.
(4) On V -> U, c(T(delta)(x))(lambda) is
s((b^{-1}(lambda))(x|V)) = s(s^{-1}(lambda(a(x|V)))) = lambda((a(x))|V).
Thus T(delta) followed by c equals a followed by delta, for arbitrary M.
This is precisely the fixed-pair morphism condition.
(5) If delta is invertible, multiply the equality by its inverse and the
reindexed inverse to obtain the inverse intertwining equation. The two
underlying inverse identities are also identities of fixed pairs. No free
basis, covering, or reflexivity assumption is used before this final condition.
-/
theorem reindexed_bidual_equivariance
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (τ : C ≌ C) [τ.functor.IsContinuous J J] [τ.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (s : (τ.functor.sheafPushforwardContinuous RingCat.{u} J J).obj
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) ≅
      (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)
    (M : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    (a : (pushforward (F := τ.functor) s.inv).obj M ≅ M) :
    (∃ q : (pushforward (F := τ.functor) s.inv).obj (homObj (R := R) M (unit _)) ≅
        homObj (R := R) ((pushforward (F := τ.functor) s.inv).obj M) (unit _),
      ∀ (U V : C) (f : V ⟶ U)
        (μ : (homObj (R := R) M (unit _)).val.obj (op (τ.functor.obj U)))
        (x : M.val.obj (op (τ.functor.obj V))),
        ((q.hom.val.app (op U) μ).app (op (Over.mk f))) x =
          s.hom.hom.app (op V) ((μ.app (op (Over.mk (τ.functor.map f)))) x)) ∧
    ∃ b : (pushforward (F := τ.functor) s.inv).obj (homObj (R := R) M (unit _)) ≅
        homObj (R := R) M (unit _),
    ∃ c : (pushforward (F := τ.functor) s.inv).obj
        (homObj (R := R) (homObj (R := R) M (unit _)) (unit _)) ≅
        homObj (R := R) (homObj (R := R) M (unit _)) (unit _),
      (∀ (U V : C) (f : V ⟶ U)
        (μ : (homObj (R := R) M (unit _)).val.obj (op (τ.functor.obj U)))
        (x : M.val.obj (op V)),
        ((b.hom.val.app (op U) μ).app (op (Over.mk f))) x =
          s.hom.hom.app (op V)
            ((μ.app (op (Over.mk (τ.functor.map f)))) (a.inv.val.app (op V) x))) ∧
      (∀ (U V : C) (f : V ⟶ U)
        (ζ : (homObj (R := R) (homObj (R := R) M (unit _)) (unit _)).val.obj
          (op (τ.functor.obj U)))
        (lam : (homObj (R := R) M (unit _)).val.obj (op V)),
        ((c.hom.val.app (op U) ζ).app (op (Over.mk f))) lam =
          s.hom.hom.app (op V)
            ((ζ.app (op (Over.mk (τ.functor.map f)))) (b.inv.val.app (op V) lam))) ∧
      (pushforward (F := τ.functor) s.inv).map (bidual M) ≫ c.hom =
        a.hom ≫ bidual M ∧
      (∃ d : Endofunctor.IsoAlgebra.mk M a ⟶
          Endofunctor.IsoAlgebra.mk (homObj (R := R) (homObj (R := R) M (unit _)) (unit _)) c,
        (Endofunctor.IsoAlgebra.forget _).map d = bidual M) ∧
      (∀ [IsIso (bidual M)],
        (pushforward (F := τ.functor) s.inv).map (inv (bidual M)) ≫ a.hom =
          c.hom ≫ inv (bidual M) ∧
        ∃ e : Endofunctor.IsoAlgebra.mk M a ≅
            Endofunctor.IsoAlgebra.mk (homObj (R := R) (homObj (R := R) M (unit _)) (unit _)) c,
          (Endofunctor.IsoAlgebra.forget _).map e.hom = bidual M ∧
          (Endofunctor.IsoAlgebra.forget _).map e.inv = inv (bidual M)) := by
  let T := pushforward (F := τ.functor) s.inv
  let D := homObj (R := R) M (unit _)
  let b := contragredient τ R s M a
  let c := contragredient τ R s D b
  constructor
  · refine ⟨reindexDualIso τ R s M, ?_⟩
    intro U V f μ x
    rw [reindexDualIso_hom, reindexDualMap_apply]
    exact reindexDualSection_apply τ R s M (op U) μ (op (Over.mk f)) x
  refine ⟨b, c, contragredient_apply τ R s M a,
    contragredient_apply τ R s D b, ?_⟩
  have heq : T.map (bidual M) ≫ c.hom = a.hom ≫ bidual M := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x : 2
    apply PresheafOfModules.hom_ext
    intro W
    ext lam
    change ((c.hom.val.app U ((bidual M).val.app (op (τ.functor.obj U.unop)) x)).app W)
      lam = _
    change ((c.hom.val.app (op U.unop)
      ((bidual M).val.app (op (τ.functor.obj U.unop)) x)).app
        (op (Over.mk W.unop.hom))) lam = _
    rw [contragredient_apply]
    change s.hom.hom.app (op W.unop.left)
      (((b.inv.val.app (op W.unop.left) lam).app
        (op (Over.mk (𝟙 (τ.functor.obj W.unop.left)))))
          (M.val.map (τ.functor.map W.unop.hom).op x)) =
      lam.app (op (Over.mk (𝟙 W.unop.left)))
        (M.val.map W.unop.hom.op (a.hom.val.app U x))
    have hb := contragredient_apply τ R s M a W.unop.left W.unop.left
      (𝟙 _) (b.inv.val.app (op W.unop.left) lam)
      (a.hom.val.app (op W.unop.left)
        (M.val.map (τ.functor.map W.unop.hom).op x))
    have hbi : b.hom.val.app (op W.unop.left)
        (b.inv.val.app (op W.unop.left) lam) = lam :=
      ConcreteCategory.congr_hom
        (congrArg (fun f : D ⟶ D ↦ f.val.app (op W.unop.left)) b.inv_hom_id) lam
    have hai : a.inv.val.app (op W.unop.left)
        (a.hom.val.app (op W.unop.left)
          (M.val.map (τ.functor.map W.unop.hom).op x)) =
        M.val.map (τ.functor.map W.unop.hom).op x :=
      ConcreteCategory.congr_hom
        (congrArg (fun f : T.obj M ⟶ T.obj M ↦ f.val.app (op W.unop.left))
          a.hom_inv_id) _
    rw [hbi, hai, τ.functor.map_id] at hb
    exact hb.symm.trans (congrArg
      (fun z ↦ lam.app (op (Over.mk (𝟙 W.unop.left))) z)
      (PresheafOfModules.naturality_apply a.hom.val W.unop.hom.op x))
  exact ⟨heq, fixedPair_inverse T a c (bidual M) heq⟩

end SheafOfModules
