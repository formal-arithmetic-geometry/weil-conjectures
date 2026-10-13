/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.SiteCechComplex
import Mathlib.CategoryTheory.Whiskering

/-! # Canonical cocones of stage Čech complexes

Source: Stacks Project, Cohomology on Sites, proof of Tag 09YP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem arrow_comp_congr {C : Type (u + 1)} [Category.{u} C]
    {a b c d : Arrow C} (ha : a = c) (hb : b = d)
    (h : a.right = b.left) (h' : c.right = d.left) :
    Arrow.mk (a.hom ≫ eqToHom h ≫ b.hom) =
      Arrow.mk (c.hom ≫ eqToHom h' ≫ d.hom) := by
  subst c
  subst d
  rfl

/-- The canonical transition maps and unit maps form a cocone of Čech complexes.
Source: Stacks Project, Cohomology on Sites, proof of Tag 09YP, displayed Čech
comparison; Sites Tag 09YM for the adjunction units.
(blueprint: lem-weil-pbc-colimit-site-cech-cocone-construction).

Proof: put B(a) = (F.map a.hom).op followed by the stage presheaf. For b : a ⟶ a',
whisker theta with (F.map a.hom).op and transport its target by
F.map_comp and a.hom ≫ b.right = a'.hom. These are natural transformations;
the identity and composition equations follow componentwise from hθid and hθcomp.
This defines a diagram B of presheaves on F.obj i. Whisker the adjunction unit,
then the inverse of E and the coprojection of c; transport the endpoint by
V's cocone naturality. Compatibility of beta with theta and naturality of c give
its cocone law. Apply S.complexFunctor to this diagram and cocone. Its degree
maps are precisely the products of these presheaf components, which gives both
projection equations. Use identity isomorphisms for eD and eK. Naturality along
S.indexMap proves commutation with the differential, already encoded by
S.complexFunctor. No colimit universal property or finite covering is used.
This works for infinite T as well; for empty T the degree maps are the unique
maps between zero groups. No choice of arbitrary data from a mere existence
statement is used by a definition: this theorem only asserts the specified data.
-/
theorem colimitSite_cech_cocone_exists
    {J : Type u} [SmallCategory J]
    (F : J ⥤ Cat.{u, u}) (P : ∀ j, Precoverage (F.obj j))
    (V : Cocone F)
    (Q : Precoverage V.pt)
    [∀ j, (V.ι.app j).toFunctor.IsContinuous (P j).toGrothendieck Q.toGrothendieck]
    (G : ∀ j, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (j k : J) (a : j ⟶ k),
      (G j).obj ⟶ (F.map a).toFunctor.op ⋙ (G k).obj)
    (hθid : ∀ (j : J) (X : F.obj j),
      Arrow.mk ((θ j j (𝟙 j)).app (op X)) = Arrow.mk (𝟙 ((G j).obj.obj (op X))))
    (hθcomp : ∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (X : F.obj j),
      Arrow.mk ((θ j l (a ≫ b)).app (op X)) =
        Arrow.mk ((θ j k a).app (op X) ≫
          (θ k l b).app (op ((F.map a).toFunctor.obj X))))
    (H : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (E : ∀ j, H.obj j ≅
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (G j)) :
    let β := fun (j : J) (X : F.obj j) ↦
      (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).unit.app (G j)).hom.app (op X)) ≫
        (E j).inv.hom.app (op ((V.ι.app j).toFunctor.obj X))
    (∀ (j k : J) (a : j ⟶ k) (X : F.obj j),
      Arrow.mk (β j X ≫ (H.map a).hom.app (op ((V.ι.app j).toFunctor.obj X))) =
        Arrow.mk ((θ j k a).app (op X) ≫ β k ((F.map a).toFunctor.obj X))) →
    ∀ (c : Cocone H),
    ∀ (i : J) {T : Type u} {U : F.obj i}
      (f : T → F.obj i) (hom : ∀ t, f t ⟶ U),
    ∀ S : SiteCechComplex f hom,
      ∃ (D : Under i ⥤ CochainComplex AddCommGrpCat.{u} ℕ)
        (eD : ∀ a : Under i, D.obj a ≅
          S.complex ((F.map a.hom).toFunctor.op ⋙ (G a.right).obj))
        (K : Cocone D)
        (eK : K.pt ≅ S.complex ((V.ι.app i).toFunctor.op ⋙ c.pt.obj)),
        (∀ (a a' : Under i) (b : a ⟶ a') (p : ℕ) (t : Fin (p + 1) → T),
          Arrow.mk ((eD a).inv.f p ≫ (D.map b).f p ≫ (eD a').hom.f p ≫
            AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
          Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
            (fun t ↦ (G a.right).obj.obj
              (op ((F.map a.hom).toFunctor.obj (S.W p t)))) t) ≫
            (θ a.right a'.right b.right).app
              (op ((F.map a.hom).toFunctor.obj (S.W p t))))) ∧
        (∀ (a : Under i) (p : ℕ) (t : Fin (p + 1) → T),
          Arrow.mk ((eD a).inv.f p ≫ (K.ι.app a).f p ≫ eK.hom.f p ≫
            AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
          Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
            (fun t ↦ (G a.right).obj.obj
              (op ((F.map a.hom).toFunctor.obj (S.W p t)))) t) ≫
            β a.right ((F.map a.hom).toFunctor.obj (S.W p t)) ≫
            (c.ι.app a.right).hom.app
              (op ((V.ι.app a.right).toFunctor.obj
                ((F.map a.hom).toFunctor.obj (S.W p t)))))) := by
  classical
  intro β hβ c i T U f hom S
  let B (a : Under i) := (F.map a.hom).toFunctor.op ⋙ (G a.right).obj
  have he {a a' : Under i} (b : a ⟶ a') :
      (F.map a.hom).toFunctor ⋙ (F.map b.right).toFunctor =
        (F.map a'.hom).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← F.map_comp, Under.w b]
  let m {a a' : Under i} (b : a ⟶ a') : B a ⟶ B a' :=
    Functor.whiskerLeft (F.map a.hom).toFunctor.op (θ a.right a'.right b.right) ≫
      eqToHom (by
        rw [← Functor.assoc]
        change ((F.map a.hom).toFunctor ⋙ (F.map b.right).toFunctor).op ⋙
          (G a'.right).obj = B a'
        rw [he b])
  have hm {a a' : Under i} (b : a ⟶ a') (X : F.obj i) :
      Arrow.mk ((m b).app (op X)) =
        Arrow.mk ((θ a.right a'.right b.right).app
          (op ((F.map a.hom).toFunctor.obj X))) := by
    simp [m, eqToHom_app]
  have hx {a a' : Under i} (b : a ⟶ a') (X : F.obj i) :
      (F.map b.right).toFunctor.obj ((F.map a.hom).toFunctor.obj X) =
        (F.map a'.hom).toFunctor.obj X := congrArg (fun G ↦ G.obj X) (he b)
  let D₀ : Under i ⥤ (F.obj i)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    { obj := B
      map := m
      map_id := by
        intro a
        apply NatTrans.ext
        funext X
        apply Arrow.mk_injective
        exact (hm (𝟙 a) X.unop).trans (hθid a.right _)
      map_comp := by
        intro a a' a'' b b'
        apply NatTrans.ext
        funext X
        apply Arrow.mk_injective
        have h₂ := (hm b' X.unop).trans
          (congrArg (fun Y ↦ Arrow.mk
            ((θ a'.right a''.right b'.right).app (op Y))) (hx b X.unop).symm)
        have hh := arrow_comp_congr (hm b X.unop) h₂ rfl rfl
        simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, Arrow.mk_hom,
          NatTrans.comp_app, op_unop] using
          (hm (b ≫ b') X.unop).trans
            ((hθcomp a.right a'.right a''.right b.right b'.right _).trans hh.symm) }
  let γ (j : J) : (G j).obj ⟶ (V.ι.app j).toFunctor.op ⋙ (H.obj j).obj :=
    ((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
      (P j).toGrothendieck Q.toGrothendieck).unit.app (G j)).hom ≫
      Functor.whiskerLeft (V.ι.app j).toFunctor.op (E j).inv.hom
  let k (a : Under i) : B a ⟶ (V.ι.app i).toFunctor.op ⋙ c.pt.obj :=
    Functor.whiskerLeft (F.map a.hom).toFunctor.op
      (γ a.right ≫ Functor.whiskerLeft (V.ι.app a.right).toFunctor.op (c.ι.app a.right).hom) ≫
      eqToHom (by
        rw [← Functor.assoc]
        change ((F.map a.hom).toFunctor ⋙ (V.ι.app a.right).toFunctor).op ⋙
          c.pt.obj = (V.ι.app i).toFunctor.op ⋙ c.pt.obj
        have hv : (F.map a.hom).toFunctor ⋙ (V.ι.app a.right).toFunctor =
            (V.ι.app i).toFunctor := congrArg Cat.Hom.toFunctor (V.w a.hom)
        rw [hv])
  have hk (a : Under i) (X : F.obj i) :
      Arrow.mk ((k a).app (op X)) = Arrow.mk
        (β a.right ((F.map a.hom).toFunctor.obj X) ≫
          (c.ι.app a.right).hom.app
            (op ((V.ι.app a.right).toFunctor.obj ((F.map a.hom).toFunctor.obj X)))) := by
    simp only [k, γ, β, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    simp only [Arrow.arrow_mk_comp_eqToHom]
    simp [Category.assoc]
  let K₀ : Cocone D₀ :=
    { pt := (V.ι.app i).toFunctor.op ⋙ c.pt.obj
      ι := { app := k
             naturality := by
               intro a a' b
               apply NatTrans.ext
               funext X
               apply Arrow.mk_injective
               let Z := (F.map a.hom).toFunctor.obj X.unop
               have h₂ := (hk a' X.unop).trans
                 (congrArg (fun Y ↦ Arrow.mk (β a'.right Y ≫
                   (c.ι.app a'.right).hom.app
                     (op ((V.ι.app a'.right).toFunctor.obj Y)))) (hx b X.unop).symm)
               have hh := arrow_comp_congr (hm b X.unop) h₂ rfl rfl
               have hv : (V.ι.app a'.right).toFunctor.obj
                   ((F.map b.right).toFunctor.obj Z) =
                     (V.ι.app a.right).toFunctor.obj Z :=
                 congrArg (fun A ↦ A.toFunctor.obj Z) (V.w b.right)
               have hι := congrArg (fun Y ↦ Arrow.mk
                 ((c.ι.app a'.right).hom.app (op Y))) hv
               have h₃ := arrow_comp_congr (hβ a.right a'.right b.right Z).symm
                 hι rfl rfl
               have hw : (H.map b.right).hom.app
                     (op ((V.ι.app a.right).toFunctor.obj Z)) ≫
                   (c.ι.app a'.right).hom.app
                     (op ((V.ι.app a.right).toFunctor.obj Z)) =
                   (c.ι.app a.right).hom.app
                     (op ((V.ι.app a.right).toFunctor.obj Z)) := by
                 have h := congrArg (fun q : H.obj a.right ⟶ c.pt ↦
                   q.hom.app (op ((V.ι.app a.right).toFunctor.obj Z))) (c.w b.right)
                 exact h
               have h₄ : Arrow.mk ((β a.right Z ≫
                   (H.map b.right).hom.app
                     (op ((V.ι.app a.right).toFunctor.obj Z))) ≫
                   (c.ι.app a'.right).hom.app
                     (op ((V.ι.app a.right).toFunctor.obj Z))) =
                 Arrow.mk (β a.right Z ≫ (c.ι.app a.right).hom.app
                     (op ((V.ι.app a.right).toFunctor.obj Z))) := by
                 rw [Category.assoc, hw]
               change Arrow.mk ((m b).app X ≫ (k a').app X) = Arrow.mk ((k a).app X)
               simpa only [D₀, NatTrans.comp_app, Arrow.mk_hom, eqToHom_refl,
                 Category.id_comp, Category.comp_id, Category.assoc, op_unop, NatTrans.id_app] using
                 hh.trans (h₃.trans (h₄.trans (hk a X.unop).symm)) } }
  let D := D₀ ⋙ S.complexFunctor
  let K := S.complexFunctor.mapCocone K₀
  refine ⟨D, fun _ ↦ Iso.refl _, K, Iso.refl _, ?_, ?_⟩
  · intro a a' b p t
    have hp : S.cochainsMap (m b) p ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ (m b).app (op (S.W p t)) := by
      apply AddCommGrpCat.ext
      intro x
      rfl
    have hh := arrow_comp_congr (rfl : Arrow.mk
      (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
        (fun t ↦ (B a).obj (op (S.W p t))) t)) = _) (hm b (S.W p t)) rfl rfl
    change Arrow.mk (𝟙 _ ≫ S.cochainsMap (m b) p ≫ 𝟙 _ ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) = _
    simp only [Category.id_comp]
    rw [hp]
    simpa only [B, Functor.comp_obj, Functor.op_obj, Arrow.mk_hom, eqToHom_refl,
      Category.id_comp, Category.comp_id] using hh
  · intro a p t
    have hp : S.cochainsMap (k a) p ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ (k a).app (op (S.W p t)) := by
      apply AddCommGrpCat.ext
      intro x
      rfl
    have hh := arrow_comp_congr (rfl : Arrow.mk
      (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
        (fun t ↦ (B a).obj (op (S.W p t))) t)) = _) (hk a (S.W p t)) rfl rfl
    change Arrow.mk (𝟙 _ ≫ S.cochainsMap (k a) p ≫ 𝟙 _ ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) = _
    simp only [Category.id_comp]
    rw [hp]
    simpa only [B, Functor.comp_obj, Functor.op_obj, Arrow.mk_hom, eqToHom_refl,
      Category.id_comp, Category.comp_id,
      Category.assoc] using hh


end CategoryTheory
