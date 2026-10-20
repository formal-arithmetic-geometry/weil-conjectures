/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurInverseImageTensorHomDefinitions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison

/-! Comparison constructions for inverse image along a scheme isomorphism. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v s h
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
attribute [local irreducible] AlgebraicGeometry.Scheme.proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
private noncomputable abbrev reindex := pushforward₀OfCommRingCat.{v} B R

private noncomputable def reindexHom :
    (pushforward₀OfCommRingCat.{max s h v} B R).obj (homObj M N) ⟶
      homObj ((reindex B R).obj M) ((reindex B R).obj N) where
  app U := ModuleCat.ofHom
    (X := ((pushforward₀OfCommRingCat.{max s h v} B R).obj (homObj M N)).obj U)
    (Y := (homObj ((reindex B R).obj M) ((reindex B R).obj N)).obj U)
    { toFun := fun φ ↦
        { app := fun W ↦ φ.app (op ((Over.post B).obj W.unop))
          naturality := by
            intro W W' f
            ext x
            exact naturality_apply φ ((Over.post B).map f.unop).op x }
      map_add' := by intros; rfl
      map_smul' := by
        intro r φ
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        rfl }
  naturality := by
    intro U V f
    ext φ : 2
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    exact restrictOver_hom_app_congr φ (B.map_comp W.unop.hom f.unop).symm x

private theorem reindexHom_injective [B.IsEquivalence] (U : Cᵒᵖ) :
    Function.Injective ((reindexHom B R M N).app U) := by
  intro φ ψ hh
  let H := Over.post (X := U.unop) B
  let Q := (Functor.whiskeringLeft _ _ AddCommGrpCat).obj H.op
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply Q.map_injective
  ext W x
  exact congrArg (fun z ↦ z.app W x) hh

private theorem reindexHom_surjective [B.IsEquivalence] (U : Cᵒᵖ) :
    Function.Surjective ((reindexHom B R M N).app U) := by
  intro ψ
  let H := Over.post (X := U.unop) B
  let Q := (Functor.whiskeringLeft _ _ AddCommGrpCat).obj H.op
  let A := (restrictOver R (B.obj U.unop)).obj M
  let E := (restrictOver R (B.obj U.unop)).obj N
  let z : A.presheaf ⟶ E.presheaf := Q.preimage ((toPresheaf _).map ψ)
  have hz := Q.map_preimage (X := A.presheaf) (Y := E.presheaf)
    ((toPresheaf _).map ψ)
  have hzlin (W : (Over U.unop)ᵒᵖ) (r : R.obj (op (H.obj W.unop).left))
      (m : M.obj (op (H.obj W.unop).left)) :
      z.app (H.op.obj W) (r • m) = r •
        (show N.obj (op (H.obj W.unop).left) from z.app (H.op.obj W) m) := by
    have he := NatTrans.congr_app hz W
    have he' (x : A.obj (H.op.obj W)) : z.app (H.op.obj W) x = ψ.app W x :=
      ConcreteCategory.congr_hom he x
    exact (he' (r • m)).trans (((ψ.app W).hom.map_smul r m).trans
      (congrArg (fun x : N.obj (op (H.obj W.unop).left) ↦ r • x) (he' m).symm))
  have hzlin' (W : (Over (B.obj U.unop))ᵒᵖ) (r : R.obj (op W.unop.left))
      (m : M.obj (op W.unop.left)) :
      z.app W (r • m) = r • (show N.obj (op W.unop.left) from z.app W m) := by
    let W' := H.op.objPreimage W
    let e := H.op.objObjPreimageIso W
    let S := (Over.forget (B.obj U.unop)).op ⋙ R
    have hinj : Function.Injective (E.presheaf.map e.inv) :=
      (ConcreteCategory.bijective_of_isIso (E.presheaf.map e.inv)).1
    apply hinj
    have hn (x : A.obj W) : E.map e.inv (z.app W x) =
        z.app (H.op.obj W') (A.map e.inv x) :=
      (ConcreteCategory.congr_hom (z.naturality e.inv) x).symm
    exact (hn (r • m)).trans <|
      (congrArg (fun x : A.obj (H.op.obj W') ↦ z.app (H.op.obj W') x)
        (A.map_smul e.inv r m)).trans <|
      (hzlin W' (S.map e.inv r) (A.map e.inv m)).trans <|
      (congrArg (fun x : E.obj (H.op.obj W') ↦ S.map e.inv r • x) (hn m).symm).trans <|
      (E.map_smul e.inv r (z.app W m)).symm
  refine ⟨homMk z hzlin', ?_⟩
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hz W) x

@[irreducible] private noncomputable def reindexHomIso [B.IsEquivalence] :
    (pushforward₀OfCommRingCat.{max s h v} B R).obj (homObj M N) ≅
      homObj ((reindex B R).obj M) ((reindex B R).obj N) := by
  have : ∀ U, IsIso ((reindexHom B R M N).app U) := fun U ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨reindexHom_injective B R M N U, reindexHom_surjective B R M N U⟩
  exact PresheafOfModules.isoMk
    (fun U ↦ asIso ((reindexHom B R M N).app U))
    (fun {_ _} f ↦ (reindexHom B R M N).naturality f)

private theorem reindexHomIso_hom [B.IsEquivalence] :
    (reindexHomIso B R M N).hom = reindexHom B R M N := by
  unfold reindexHomIso
  rfl

end AlgebraicGeometry.Scheme.PurHom
namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (c : S ⟶ R) (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
private noncomputable abbrev restrict :=
  restrictScalars.{v} (Functor.whiskerRight c (forget₂ CommRingCat RingCat))
private noncomputable def restrictHom :
    (restrict.{u, max s h v} c).obj (homObj M N) ⟶
      homObj ((restrict c).obj M) ((restrict c).obj N) where
  app U := ModuleCat.ofHom
    (X := ((restrict.{u, max s h v} c).obj (homObj M N)).obj U)
    (Y := (homObj ((restrict c).obj M) ((restrict c).obj N)).obj U)
    { toFun := fun φ ↦
        { app := fun W ↦ (ModuleCat.restrictScalars (c.app (op W.unop.left)).hom).map
            (φ.app W)
          naturality := by
            intro W W' f
            ext x
            exact naturality_apply φ f x }
      map_add' := by intros; rfl
      map_smul' := by
        intro r φ
        apply PresheafOfModules.hom_ext
        intro W
        ext x
        change R.map W.unop.hom.op (c.app U r) • (show N.obj (op W.unop.left) from φ.app W x) =
          c.app (op W.unop.left) (S.map W.unop.hom.op r) •
            (show N.obj (op W.unop.left) from φ.app W x)
        congr 1
        exact ConcreteCategory.congr_hom (c.naturality W.unop.hom.op).symm r }
  naturality := by
    intro U V f
    ext φ : 2
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    rfl

private theorem restrictHom_injective (U : Cᵒᵖ) :
    Function.Injective ((restrictHom c M N).app U) := by
  intro φ ψ h
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  exact congrArg (fun z ↦ z.app W x) h

private theorem restrictHom_surjective [IsIso c] (U : Cᵒᵖ) :
    Function.Surjective ((restrictHom c M N).app U) := by
  intro ψ
  let z : (restrictOver R U.unop).obj M ⟶ (restrictOver R U.unop).obj N :=
    homMk ((toPresheaf ((Over.forget U.unop).op ⋙ S ⋙ forget₂ CommRingCat RingCat)).map ψ) (by
      intro W r m
      obtain ⟨r', rfl⟩ := (ConcreteCategory.bijective_of_isIso
        (c.app (op W.unop.left))).2 r
      exact (ψ.app W).hom.map_smul r' m)
  refine ⟨z, ?_⟩
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

@[irreducible] private noncomputable def restrictHomIso [IsIso c] :
    (restrict.{u, max s h v} c).obj (homObj M N) ≅
      homObj ((restrict c).obj M) ((restrict c).obj N) := by
  have : ∀ U, IsIso ((restrictHom c M N).app U) := fun U ↦
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨restrictHom_injective c M N U, restrictHom_surjective c M N U⟩
  exact PresheafOfModules.isoMk
    (fun U ↦ asIso ((restrictHom c M N).app U))
    (fun {_ _} f ↦ (restrictHom c M N).naturality f)
private theorem restrictHomIso_hom [IsIso c] :
    (restrictHomIso c M N).hom = restrictHom c M N := by
  unfold restrictHomIso
  rfl

end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) [B.IsEquivalence] (R : Dᵒᵖ ⥤ CommRingCat.{u}) {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (c : S ⟶ B.op ⋙ R) [IsIso c]
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
@[irreducible] private noncomputable def pushHomIso :
    (PresheafOfModules.pushforward.{max s h v}
      (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj (homObj M N) ≅
      homObj
        ((PresheafOfModules.pushforward.{v}
          (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj M)
        ((PresheafOfModules.pushforward.{v}
          (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj N) :=
  (restrict.{u, max s h v} c).mapIso (reindexHomIso B R M N) ≪≫
    restrictHomIso c ((reindex B R).obj M) ((reindex B R).obj N)

private theorem pushHomIso_hom :
    (pushHomIso B R c M N).hom =
      (restrict.{u, max s h v} c).map (reindexHom B R M N) ≫
        restrictHom c ((reindex B R).obj M) ((reindex B R).obj N) := by
  unfold pushHomIso
  change (restrict.{u, max s h v} c).map (reindexHomIso B R M N).hom ≫
    (restrictHomIso c ((reindex B R).obj M) ((reindex B R).obj N)).hom = _
  rw [reindexHomIso_hom, restrictHomIso_hom]

end AlgebraicGeometry.Scheme.PurHom



namespace AlgebraicGeometry.Scheme.PurHom
private noncomputable def homCongr {C : Type s} [Category.{h} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    {F F' G G' : SheafOfModules.{v} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : F ≅ F') (b : G ≅ G') :
    SheafOfModules.homObj (R := R) F G ≅ SheafOfModules.homObj (R := R) F' G' where
  hom := SheafOfModules.homObjMap (R := R) a.inv b.hom
  inv := SheafOfModules.homObjMap (R := R) a.hom b.inv
  hom_inv_id := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R),
      a.hom_inv_id, b.hom_inv_id, SheafOfModules.homObjMap_id (R := R)]
  inv_hom_id := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R),
      a.inv_hom_id, b.inv_hom_id, SheafOfModules.homObjMap_id (R := R)]

private theorem inverse_square {C : Type s} [Category.{h} C]
    {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ e'.hom = e.hom ≫ b) : b ≫ e'.inv = e.inv ≫ a := by
  apply (cancel_epi e.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem homCongr_naturality {C : Type s} [Category.{h} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    {F F' G G' P P' Q Q' : SheafOfModules.{v} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (eF : F ≅ P) (eF' : F' ≅ P') (eG : G ≅ Q) (eG' : G' ≅ Q')
    (a : F' ⟶ F) (b : G ⟶ G') (a' : P' ⟶ P) (b' : Q ⟶ Q')
    (ha : a ≫ eF.hom = eF'.hom ≫ a') (hb : b ≫ eG'.hom = eG.hom ≫ b') :
    SheafOfModules.homObjMap (R := R) a b ≫ (homCongr R eF' eG').hom =
      (homCongr R eF eG).hom ≫ SheafOfModules.homObjMap (R := R) a' b' := by
  change SheafOfModules.homObjMap (R := R) a b ≫
      SheafOfModules.homObjMap (R := R) eF'.inv eG'.hom =
    SheafOfModules.homObjMap (R := R) eF.inv eG.hom ≫
      SheafOfModules.homObjMap (R := R) a' b'
  rw [SheafOfModules.homObjMap_comp_homObjMap,
    SheafOfModules.homObjMap_comp_homObjMap]
  exact congrArg₂ (SheafOfModules.homObjMap (R := R))
    (inverse_square eF' eF a a' ha).symm hb

private theorem mate_isIso {C : Type s} {D : Type h} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) [R.ReflectsIsomorphisms]
    {M : C} {N : D} [IsIso (a.unit.app M)] (e : M ≅ R.obj N) :
    IsIso ((a.homEquiv M N).symm e.hom) := by
  have he : R.map ((a.homEquiv M N).symm e.hom) =
      inv (a.unit.app M) ≫ e.hom := by
    apply (cancel_epi (a.unit.app M)).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact (a.homEquiv M N).apply_symm_apply e.hom
  have : IsIso (R.map ((a.homEquiv M N).symm e.hom)) := by rw [he]; infer_instance
  exact isIso_of_reflects_iso _ R
end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
private def liftIso {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{v} R}
    (e : M.val ≅ N.val) : M ≅ N where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := SheafOfModules.hom_ext e.hom_inv_id
  inv_hom_id := SheafOfModules.hom_ext e.inv_hom_id

set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private noncomputable def sheafPushHomIso
    {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
    (B : C ⥤ D) [B.IsEquivalence]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [B.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf K CommRingCat.{u}) (S : Sheaf J CommRingCat.{u})
    (c : S ⟶ (B.sheafPushforwardContinuous CommRingCat.{u} J K).obj R) [IsIso c]
    (M N : SheafOfModules.{v} ((sheafCompose K
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    let p : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S ⟶
        (B.sheafPushforwardContinuous RingCat.{u} J K).obj
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
      ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩
    (SheafOfModules.pushforward.{max s h v} p).obj
        (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := S)
        ((SheafOfModules.pushforward.{v} p).obj M)
        ((SheafOfModules.pushforward.{v} p).obj N) := by
  let c₀ : S.obj ⟶ B.op ⋙ R.obj := c.hom
  have : IsIso c₀ := (sheafToPresheaf J CommRingCat.{u}).map_isIso c
  let e := pushHomIso B R.obj c₀ M.val N.val
  dsimp only
  let p : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S ⟶
      (B.sheafPushforwardContinuous RingCat.{u} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩
  exact liftIso
    (M := (SheafOfModules.pushforward.{max s h v} p).obj
      (SheafOfModules.homObj (R := R) M N))
    (N := SheafOfModules.homObj (R := S)
      ((SheafOfModules.pushforward.{v} p).obj M)
      ((SheafOfModules.pushforward.{v} p).obj N)) e

private theorem sheafPushHomIso_apply
    {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
    (B : C ⥤ D) [B.IsEquivalence]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [B.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf K CommRingCat.{u}) (S : Sheaf J CommRingCat.{u})
    (c : S ⟶ (B.sheafPushforwardContinuous CommRingCat.{u} J K).obj R) [IsIso c]
    (M N : SheafOfModules.{v} ((sheafCompose K
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) (φ : (PresheafOfModules.homObj M.val N.val).obj (B.op.obj U))
    (W : (Over U.unop)ᵒᵖ) (x : M.val.obj (op (B.obj W.unop.left))) :
    (((sheafPushHomIso B J K R S c M N).hom.val.app U φ).app W) x =
      φ.app (op ((Over.post B).obj W.unop)) x := by
  let c₀ : S.obj ⟶ B.op ⋙ R.obj := c.hom
  have : IsIso c₀ := (sheafToPresheaf J CommRingCat.{u}).map_isIso c
  unfold sheafPushHomIso
  change (((pushHomIso B R.obj c₀ M.val N.val).hom.app U φ).app W) x = _
  exact congrArg (fun f ↦ ((f.app U φ).app W) x)
    (pushHomIso_hom B R.obj c₀ M.val N.val)

private theorem push_reflects_generic
    {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
    (B : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [B.IsContinuous J K]
    (R : Sheaf K RingCat.{u}) (S : Sheaf J RingCat.{u})
    (c : S ⟶ (B.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    [(B.sheafPushforwardContinuous AddCommGrpCat.{v} J K).ReflectsIsomorphisms] :
    (SheafOfModules.pushforward.{v} c).ReflectsIsomorphisms := by
  let P := SheafOfModules.toSheaf.{v} S
  let Q := SheafOfModules.toSheaf.{v} R
  refine ⟨fun {M N} f hf ↦ ?_⟩
  have hp : IsIso (P.map ((SheafOfModules.pushforward.{v} c).map f)) := P.map_isIso _
  have hp' : IsIso ((B.sheafPushforwardContinuous AddCommGrpCat.{v} J K).map
      (Q.map f)) := hp
  have : IsIso (Q.map f) := isIso_of_reflects_iso _
    (B.sheafPushforwardContinuous AddCommGrpCat.{v} J K)
  exact isIso_of_reflects_iso f Q

end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
section GenericAdjunction
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) [B.IsEquivalence]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [B.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf K CommRingCat.{u}) (S : Sheaf J CommRingCat.{u})
  (c : S ⟶ (B.sheafPushforwardContinuous CommRingCat.{u} J K).obj R) [IsIso c]
private noncomputable abbrev push := SheafOfModules.pushforward.{max s h u}
  (F := B) (J := J) (K := K)
  (S := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
  (R := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩
variable (L : SheafOfModules.{max s h u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{max s h u} ((sheafCompose K
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  (adj : L ⊣ (SheafOfModules.pushforward.{max s h u} (F := B) (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩))
  (hunit : ∀ M, IsIso (adj.unit.app M))
  [hreflect : ((SheafOfModules.pushforward.{max s h u} (F := B) (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩)).ReflectsIsomorphisms]
private noncomputable abbrev sourceRing :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S
private noncomputable abbrev targetRing :=
  (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R

@[irreducible] private noncomputable def genericPushComparison
    (M N : SheafOfModules.{max s h u} (targetRing K R)) :
    (push B J K R S c).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := S)
        ((push B J K R S c).obj M) ((push B J K R S c).obj N) :=
  sheafPushHomIso B J K R S c M N

omit hreflect in
private theorem genericPushComparison_apply
    (M N : SheafOfModules.{max s h u} (targetRing K R))
    (V W : C) (a : W ⟶ V)
    (φ : (SheafOfModules.homObj (R := R) M N).val.obj (op (B.obj V)))
    (x : M.val.obj (op (B.obj W))) :
    (((genericPushComparison B J K R S c M N).hom.val.app (op V) φ).app
      (op (Over.mk a))) x = φ.app (op (Over.mk (B.map a))) x := by
  unfold genericPushComparison
  exact sheafPushHomIso_apply B J K R S c M N (op V) φ (op (Over.mk a)) x

@[irreducible] private noncomputable def unitIso (M : SheafOfModules.{max s h u} (sourceRing J S)) :
    M ≅ (push B J K R S c).obj (L.obj M) := by
  exact @asIso (SheafOfModules.{max s h u} (sourceRing J S)) _ M
    ((push B J K R S c).obj (L.obj M))
    (adj.unit.app M) (hunit M)


omit [B.IsEquivalence] [IsIso c] hreflect in
private theorem unitIso_hom (M : SheafOfModules.{max s h u} (sourceRing J S)) :
    (unitIso B J K R S c L adj hunit M).hom = adj.unit.app M := by
  unfold unitIso
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit hreflect in
private theorem genericPushComparison_naturality
    {M M' N N' : SheafOfModules.{max s h u} (targetRing K R)}
    (a : M' ⟶ M) (b : N ⟶ N') :
    (push B J K R S c).map (SheafOfModules.homObjMap
        (R := R) a b) ≫
      (genericPushComparison B J K R S c M' N').hom =
    (genericPushComparison B J K R S c M N).hom ≫
      SheafOfModules.homObjMap (R := S) ((push B J K R S c).map a) ((push B J K R S c).map b) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  change (((genericPushComparison B J K R S c M' N').hom.val.app U
    ((SheafOfModules.homObjMap
      (R := R) a b).val.app
        (B.op.obj U) φ)).app W) x =
    b.val.app (op (B.obj W.unop.left))
      ((((genericPushComparison B J K R S c M N).hom.val.app U φ).app W)
        (a.val.app (op (B.obj W.unop.left)) x))
  exact (genericPushComparison_apply B J K R S c M' N' U.unop W.unop.left W.unop.hom
    ((SheafOfModules.homObjMap
      (R := R) a b).val.app
        (B.op.obj U) φ) x).trans
      (congrArg (fun t ↦ b.val.app (op (B.obj W.unop.left)) t)
        (genericPushComparison_apply B J K R S c M N U.unop W.unop.left W.unop.hom φ
          (a.val.app (op (B.obj W.unop.left)) x)).symm)

@[irreducible] private noncomputable def homUnit
    (F G : SheafOfModules.{max s h u} (sourceRing J S)) :
    SheafOfModules.homObj (R := S) F G ≅
      (push B J K R S c).obj (SheafOfModules.homObj
        (R := R)
        (L.obj F)
        (L.obj G)) :=
  homCongr S (unitIso B J K R S c L adj hunit F) (unitIso B J K R S c L adj hunit G) ≪≫
    (genericPushComparison B J K R S c _ _).symm

@[irreducible] private noncomputable def comparisonMap
    (F G : SheafOfModules.{max s h u} (sourceRing J S)) :
    L.obj (SheafOfModules.homObj (R := S) F G) ⟶
      SheafOfModules.homObj
        (R := R)
        (L.obj F)
        (L.obj G) :=
  (adj.homEquiv _ _).symm (homUnit B J K R S c L adj hunit F G).hom

omit hreflect in
private theorem comparisonMap_unit (F G : SheafOfModules.{max s h u} (sourceRing J S)) :
    (adj.homEquiv _ _) (comparisonMap B J K R S c L adj hunit F G) =
      (homUnit B J K R S c L adj hunit F G).hom := by
  unfold comparisonMap
  exact (adj.homEquiv _ _).apply_symm_apply _

@[irreducible] private noncomputable def comparisonIso
    (F G : SheafOfModules.{max s h u} (sourceRing J S)) :
    L.obj (SheafOfModules.homObj (R := S) F G) ≅
      SheafOfModules.homObj
        (R := R)
        (L.obj F)
        (L.obj G) := by
  have hi := @mate_isIso _ _ _ _ L (push B J K R S c)
    adj (inferInstance : (push B J K R S c).ReflectsIsomorphisms)
    (SheafOfModules.homObj (R := S) F G)
    (SheafOfModules.homObj
      (R := R)
      (L.obj F) (L.obj G))
    (hunit (SheafOfModules.homObj (R := S) F G)) (homUnit B J K R S c L adj hunit F G)
  exact @asIso _ _ _ _ (comparisonMap B J K R S c L adj hunit F G) (by
    unfold comparisonMap
    exact hi)

private theorem comparisonIso_hom (F G : SheafOfModules.{max s h u} (sourceRing J S)) :
    (comparisonIso B J K R S c L adj hunit F G).hom = comparisonMap B J K R S c L adj
      hunit F G := by
  unfold comparisonIso
  rfl

omit hreflect in
private theorem homUnit_naturality
    {F F' G G' : SheafOfModules.{max s h u} (sourceRing J S)} (a : F' ⟶ F) (b : G ⟶ G') :
    SheafOfModules.homObjMap (R := S) a b ≫ (homUnit B J K R S c L adj hunit F' G').hom =
      (homUnit B J K R S c L adj hunit F G).hom ≫ (push B J K R S c).map
        (SheafOfModules.homObjMap
          (R := R)
          (L.map a)
          (L.map b)) := by
  have hu := homCongr_naturality S
    (unitIso B J K R S c L adj hunit F) (unitIso B J K R S c L adj hunit F') (unitIso B J K R S c
      L adj hunit G) (unitIso B J K R S c L adj hunit G')
    a b ((push B J K R S c).map (L.map a))
    ((push B J K R S c).map (L.map b))
    (by
      rw [unitIso_hom B J K R S c L adj hunit F,
        unitIso_hom B J K R S c L adj hunit F']
      exact adj.unit.naturality a)
    (by
      rw [unitIso_hom B J K R S c L adj hunit G,
        unitIso_hom B J K R S c L adj hunit G']
      exact adj.unit.naturality b)
  have hp := inverse_square (genericPushComparison B J K R S c _ _) (genericPushComparison B J K R
    S c _ _)
    ((push B J K R S c).map (SheafOfModules.homObjMap
      (R := R)
      (L.map a) (L.map b)))
    (SheafOfModules.homObjMap (R := S)
      ((push B J K R S c).map (L.map a))
      ((push B J K R S c).map (L.map b)))
    (genericPushComparison_naturality B J K R S c _ _)
  unfold homUnit
  change SheafOfModules.homObjMap (R := S) a b ≫
      ((homCongr S (unitIso B J K R S c L adj hunit F') (unitIso B J K R S c L adj hunit G')).hom ≫
        (genericPushComparison B J K R S c _ _).inv) =
    ((homCongr S (unitIso B J K R S c L adj hunit F) (unitIso B J K R S c L adj hunit G)).hom ≫
        (genericPushComparison B J K R S c _ _).inv) ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ (genericPushComparison B J K R S c _ _).inv) hu).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ (homCongr S (unitIso B J K R S c L adj hunit F) (unitIso B J K R S c L
          adj hunit G)).hom ≫ z) hp).trans
          (Category.assoc _ _ _).symm)))

private theorem comparisonIso_naturality
    {F F' G G' : SheafOfModules.{max s h u} (sourceRing J S)} (a : F' ⟶ F) (b : G ⟶ G') :
    L.map (SheafOfModules.homObjMap (R := S) a b) ≫
        (comparisonIso B J K R S c L adj hunit F' G').hom =
      (comparisonIso B J K R S c L adj hunit F G).hom ≫ SheafOfModules.homObjMap
        (R := R)
        (L.map a)
        (L.map b) := by
  simp only [comparisonIso_hom]
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rw [comparisonMap_unit, comparisonMap_unit]
  exact homUnit_naturality B J K R S c L adj hunit a b

private theorem comparisonIso_section (F G : SheafOfModules.{max s h u} (sourceRing J S))
    (V W : C) (a : W ⟶ V)
    (φ : (SheafOfModules.homObj (R := S) F G).val.obj (op V))
    (s : F.val.obj (op W)) :
    ((comparisonIso B J K R S c L adj hunit F G).hom.val.app (op (B.obj V))
      ((unitIso B J K R S c L adj hunit (SheafOfModules.homObj (R := S) F G)).hom.val.app (op V)
        φ)).app
        (op (Over.mk (B.map a)))
          ((unitIso B J K R S c L adj hunit F).hom.val.app (op W) s) =
      (unitIso B J K R S c L adj hunit G).hom.val.app (op W) (φ.app (op (Over.mk a)) s) := by
  let vφ := (unitIso B J K R S c L adj hunit (SheafOfModules.homObj (R := S) F G)).hom.val.app (op
    V) φ
  let vs := (unitIso B J K R S c L adj hunit F).hom.val.app (op W) s
  let ev := fun φ' s' ↦
    ((comparisonMap B J K R S c L adj hunit F G).val.app (op (B.obj V)) φ').app
      (op (Over.mk (B.map a))) s'
  have he : (unitIso B J K R S c L adj hunit (SheafOfModules.homObj (R := S) F G)).hom ≫
      (push B J K R S c).map (comparisonMap B J K R S c L adj hunit F G) ≫ (genericPushComparison
        B J K R S c _ _).hom =
    SheafOfModules.homObjMap (R := S) (unitIso B J K R S c L adj hunit F).inv (unitIso B J K R S c
      L adj hunit G).hom := by
    rw [unitIso_hom, ← Category.assoc]
    change (adj.homEquiv _ _) (comparisonMap B J K R S c L adj hunit F G) ≫
      (genericPushComparison B J K R S c _ _).hom = _
    rw [comparisonMap_unit]
    simp only [homUnit, homCongr, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have he' := congrArg (fun z ↦ (z.val.app (op V) φ).app (op (Over.mk a)) vs) he
  have hp := genericPushComparison_apply B J K R S c
    (L.obj F) (L.obj G)
    V W a (((push B J K R S c).map (comparisonMap B J K R S c L adj hunit F G)).val.app (op V) vφ)
      vs
  have hm : ev vφ vs = (unitIso B J K R S c L adj hunit G).hom.val.app (op W)
      (φ.app (op (Over.mk a)) ((unitIso B J K R S c L adj hunit F).inv.val.app (op W) vs)) :=
    hp.symm.trans he'
  have hinv : (unitIso B J K R S c L adj hunit F).inv.val.app (op W) vs = s :=
    congrArg (fun z ↦ z.val.app (op W) s) (unitIso B J K R S c L adj hunit F).hom_inv_id
  have ht := congrArg
    (fun t ↦ (unitIso B J K R S c L adj hunit G).hom.val.app (op W) (φ.app (op (Over.mk a)) t)) hinv
  have hc := congrArg (fun z ↦ (z.val.app (op (B.obj V))
      ((unitIso B J K R S c L adj hunit (SheafOfModules.homObj (R := S) F G)).hom.val.app (op V)
        φ)).app
        (op (Over.mk (B.map a))) ((unitIso B J K R S c L adj hunit F).hom.val.app (op W) s))
    (comparisonIso_hom B J K R S c L adj hunit F G)
  exact hc.trans (hm.trans ht)

end GenericAdjunction
end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
private instance commRingSheafify (Z : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology Z) CommRingCat.{u + 1} := inferInstance
private instance abelianSheafify (Z : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology Z) AddCommGrpCat.{u + 1} := inferInstance
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
private abbrev YRing : Sheaf (ProEt.topology Y) RingCat.{u + 1} :=
  (sheafCompose (ProEt.topology Y)
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
private noncomputable abbrev XRing : Sheaf (ProEt.topology X) RingCat.{u + 1} :=
  (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)

set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChange_equivalence : (proEtaleBaseChange g).IsEquivalence := by
  have : MorphismProperty.IsStableUnderComposition (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence := by
    change (proEtaleIsoPostcompose g).IsEquivalence
    exact (proEtaleIsoPostcompose_equivalence g).1
  exact (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial).isEquivalence_right_of_isEquivalence_left

private theorem ringUnit_iso :
    IsIso ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O) := by
  have : IsIso (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g CommRingCat.{u + 1}).2.1
  exact NatIso.isIso_app_of_isIso _ O

private theorem unit_iso (M : SheafOfModules.{u + 1} (YRing O)) :
    @IsIso (SheafOfModules.{u + 1} (YRing O)) _ M
      ((T g O).obj ((proEtaleModuleInverseImage g O).obj M))
      ((canonicalAdjunction g O).unit.app M) := by
  let P := SheafOfModules.toSheaf.{u + 1} (YRing O)
  let Q := SheafOfModules.toSheaf.{u + 1} (XRing g O)
  let b := proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}
  have h := proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g AddCommGrpCat.{u + 1}
  have : IsIso b.unit := h.2.1
  let e := (b.homEquiv (P.obj M)
    (Q.obj ((proEtaleModuleInverseImage g O).obj M))).symm
      (P.map ((canonicalAdjunction g O).unit.app M))
  have : IsIso e := proEtaleModuleInverseImage_unitComparison_isIso g O
    (canonicalAdjunction g O) M
  have he : P.map ((canonicalAdjunction g O).unit.app M) =
      b.unit.app (P.obj M) ≫ (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map e :=
    ((b.homEquiv (P.obj M)
      (Q.obj ((proEtaleModuleInverseImage g O).obj M))).apply_symm_apply
        (P.map ((canonicalAdjunction g O).unit.app M))).symm
  have hu : IsIso (b.unit.app (P.obj M)) := NatIso.isIso_app_of_isIso b.unit (P.obj M)
  have hm : IsIso ((proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map e) :=
    (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map_isIso e
  have : IsIso (P.map ((canonicalAdjunction g O).unit.app M)) := by
    rw [he]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hu hm
  exact isIso_of_reflects_iso ((canonicalAdjunction g O).unit.app M) P

private theorem push_reflects : (T g O).ReflectsIsomorphisms := by
  have h := proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g AddCommGrpCat.{u + 1}
  have : PreservesLimitsOfSize.{0, 0}
      (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) := h.2.2.2.1
  let : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).IsEquivalence := h.1
  let : (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).IsEquivalence :=
    (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).isEquivalence_right_of_isEquivalence_left
  have hR : (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).ReflectsIsomorphisms :=
    inferInstance
  exact @push_reflects_generic _ _ _ _ (proEtaleBaseChange g)
    (ProEt.topology Y) (ProEt.topology X) _ (XRing g O) (YRing O)
    ⟨Functor.whiskerRight ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ hR


end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme

/-- The normalized internal-Hom comparison and its two-variable naturality.
Source: Stacks Project, `sites-modules.tex`, Tags 04IX, 04TT and 0GMX
(blueprint: lem-pur-inverse-image-hom-comparison).
Proof: identify the recorded inverse image with reindexing along the inverse site
equivalence. At an object U the equivalence induces an equivalence of slice sites.
Restriction of the coefficient ring and of both modules commutes with this
reindexing. Precomposition therefore gives mutually inverse linear maps between
natural transformations of restricted modules. They form a sheaf isomorphism,
since restriction to a smaller slice is precomposition on both sides. Transport
back through the canonical unit-normalized inverse-image identification. Evaluation
at an arrow a and a unit section s gives precisely the first displayed equation.
For maps a and b in the two variables, both naturality composites are the
transformation obtained by postcomposing with b and precomposing with a on every
slice component, proving the second equation. This applies also to the empty site
and the zero ring, and needs no finite-presentation assumption. -/
theorem purInverseImageHomComparison
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ∃ η : ∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
        (proEtaleModuleInverseImage g O).obj
            (SheafOfModules.homObj (R := O) F G) ≅
          SheafOfModules.homObj
            (R := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
            ((proEtaleModuleInverseImage g O).obj F)
            ((proEtaleModuleInverseImage g O).obj G),
        (∀ (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (V W : Y.ProEt) (a : W ⟶ V)
            (φ : (SheafOfModules.homObj (R := O) F G).val.obj (op V))
            (s : F.val.obj (op W)),
          ((η F G).hom.val.app (op ((proEtaleBaseChange g).obj V))
            (purInverseImageSection g O _ V φ)).app
              (op (Over.mk ((proEtaleBaseChange g).map a)))
                (purInverseImageSection g O F W s) =
          purInverseImageSection g O G W (φ.app (op (Over.mk a)) s)) ∧
        (∀ (F F' G G' : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
            (a : F' ⟶ F) (b : G ⟶ G'),
            (proEtaleModuleInverseImage g O).map
                (SheafOfModules.homObjMap (R := O) a b) ≫
              (η F' G').hom =
            (η F G).hom ≫
              SheafOfModules.homObjMap
                (R := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
                ((proEtaleModuleInverseImage g O).map a)
                ((proEtaleModuleInverseImage g O).map b)) := by
  let : (proEtaleBaseChange g).IsEquivalence := PurHom.baseChange_equivalence g
  let : IsIso ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O) :=
    PurHom.ringUnit_iso g O
  let : (T g O).ReflectsIsomorphisms := PurHom.push_reflects g O
  let B := proEtaleBaseChange g
  let R := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O
  let c := (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O
  let L := proEtaleModuleInverseImage g O
  let adj := canonicalAdjunction g O
  let hunit := PurHom.unit_iso g O
  let : IsIso c := PurHom.ringUnit_iso g O
  let : (PurHom.push B (ProEt.topology Y) (ProEt.topology X) R O c).ReflectsIsomorphisms :=
    PurHom.push_reflects g O
  refine ⟨fun F G ↦ @PurHom.comparisonIso _ _ _ _ B
    (PurHom.baseChange_equivalence g) (ProEt.topology Y) (ProEt.topology X) _ _ _ R O c
    (PurHom.ringUnit_iso g O) L adj hunit (PurHom.push_reflects g O) F G, ?_, ?_⟩
  · intro F G V W a φ x
    have h := @PurHom.comparisonIso_section _ _ _ _ B
      (PurHom.baseChange_equivalence g) (ProEt.topology Y) (ProEt.topology X) _ _ _ R O c
      (PurHom.ringUnit_iso g O) L adj hunit (PurHom.push_reflects g O) F G V W a φ x
    have hsec (M : SheafOfModules.{u + 1} (PurHom.YRing O))
        (V : Y.ProEt) (x : M.val.obj (op V)) :
        (PurHom.unitIso B (ProEt.topology Y) (ProEt.topology X) R O c
          L adj hunit M).hom.val.app (op V) x = purInverseImageSection g O M V x := by
      rw [PurHom.unitIso_hom B (ProEt.topology Y) (ProEt.topology X) R O c L adj hunit M]
      exact canonicalUnit_sections g O M (op V) x
    have h' := h.trans (hsec G W (φ.app (op (Over.mk a)) x))
    simpa only [hsec] using h'
  · intro F F' G G' a b
    exact @PurHom.comparisonIso_naturality _ _ _ _ B
      (PurHom.baseChange_equivalence g) (ProEt.topology Y) (ProEt.topology X) _ _ _ R O c
      (PurHom.ringUnit_iso g O) L adj hunit (PurHom.push_reflects g O) F F' G G' a b

end AlgebraicGeometry.Scheme
