/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Local morphisms of module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T, proof of (1).
(blueprint: lem-sf-local-module-hom-sheaf).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} (M N : SheafOfModules.{u} R)

set_option backward.isDefEq.respectTransparency false in
/-- The linear local morphisms inside the presheaf of additive local morphisms. -/
def localHomSubfunctor : Subfunctor (presheafHom M.val.presheaf N.val.presheaf) where
  obj U := {a | ∀ (V : Over U.unop) (r : R.obj.obj (op V.left))
    (x : M.val.obj (op V.left)), a.app (op V) (r • x) =
      r • (show N.val.obj (op V.left) from a.app (op V) x)}
  map f _a ha V r x := ha ((Over.map f.unop).obj V) r x

/-- Local module morphisms, with restriction by precomposition on slices. -/
abbrev localHom : Cᵒᵖ ⥤ Type u := (localHomSubfunctor M N).toFunctor

/-- The concrete local morphisms are exactly morphisms on the ringed slice. -/
def localHomEquiv (U : Cᵒᵖ) :
    (localHom M N).obj U ≃ (M.over U.unop ⟶ N.over U.unop) where
  toFun a := ⟨PresheafOfModules.homMk a.1 (fun V r x ↦ a.2 V.unop r x)⟩
  invFun a := ⟨(PresheafOfModules.toPresheaf _).map a.val,
    fun V r x ↦ (a.val.app (op V)).hom.map_smul r x⟩
  left_inv a := by apply Subtype.ext; apply NatTrans.ext; funext V; ext x; rfl
  right_inv a := by ext V x; rfl

lemma localHomEquiv_map_app {U V : C} (f : V ⟶ U)
    (a : (localHom M N).obj (op U)) (x : M.val.obj (op V)) :
    (localHomEquiv M N (op V) ((localHom M N).map f.op a)).val.app
        (op (Over.mk (𝟙 V))) x =
      (localHomEquiv M N (op U) a).val.app (op (Over.mk f)) x :=
  ConcreteCategory.congr_hom (presheafHom_map_app (𝟙 V) f f (Category.id_comp f) a.val) x

/-- Linearity can be checked locally, so the local module Hom presheaf is a sheaf. -/
theorem localHom_isSheaf : Presheaf.IsSheaf J (localHom M N) := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).1 (N.isSheaf.hom M.val.presheaf))).2
  intro U a ha V r x
  apply N.isSheaf.isSeparated _ _ (J.pullback_stable V.hom ha)
  intro W f hf
  have h := hf
  change ((presheafHom M.val.presheaf N.val.presheaf).map (f ≫ V.hom).op a) ∈
    (localHomSubfunctor M N).obj (op W) at h
  have hh := h (Over.mk (𝟙 W)) (R.obj.map f.op r) (M.val.map f.op x)
  have hn := a.naturality (Over.homMk f : Over.mk (f ≫ V.hom) ⟶ V).op
  have hn' (y : M.val.obj (op V.left)) :
      a.app (op (Over.mk (f ≫ V.hom))) (M.val.map f.op y) =
        N.val.map f.op (a.app (op V) y) := ConcreteCategory.congr_hom hn y
  change N.val.map f.op (a.app (op V) (r • x)) =
    N.val.map f.op (r • (show N.val.obj (op V.left) from a.app (op V) x))
  rw [← hn', M.val.map_smul, N.val.map_smul]
  have he := presheafHom_map_app (𝟙 W) (f ≫ V.hom) (f ≫ V.hom)
    (Category.id_comp _) a
  rw [he] at hh
  exact hh.trans (congrArg (fun y : N.val.obj (op W) ↦ R.obj.map f.op r • y) (hn' x))

/-- Composition of local module morphisms. -/
def localHomComp (P : SheafOfModules.{u} R) {U : Cᵒᵖ}
    (a : (localHom M N).obj U) (b : (localHom N P).obj U) : (localHom M P).obj U :=
  (localHomEquiv M P U).symm (localHomEquiv M N U a ≫ localHomEquiv N P U b)

/-- The local identity morphism. -/
def localHomId (U : Cᵒᵖ) : (localHom M M).obj U :=
  (localHomEquiv M M U).symm (𝟙 _)

lemma localHomComp_map (P : SheafOfModules.{u} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (localHom M N).obj U) (b : (localHom N P).obj U) :
    (localHom M P).map f (localHomComp M N P a b) =
      localHomComp M N P ((localHom M N).map f a) ((localHom N P).map f b) := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  ext x
  rfl

lemma localHomId_map {U V : Cᵒᵖ} (f : U ⟶ V) :
    (localHom M M).map f (localHomId M U) = localHomId M V := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  ext x
  rfl

end SheafOfModules
