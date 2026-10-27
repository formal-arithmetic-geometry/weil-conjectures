/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.SchemeUnramifiedEtaleLocality
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas

/-! # Isomorphism spaces of Deligne--Mumford stacks are unramified

Source: Stacks Project, Tags 06N3, 06MB(1), 045G, 04SI and 03ZJ
(blueprint: lem-sfb-dm-isom-space-unramified).

A space over `T` is encoded by a space over `S` with a map to `h_T`.
The representing bijections are supplied for all pullback lifts. Their compatibility
with further lifts is the naturality of the Isom functor, without choosing a cleavage.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry Opposite

namespace CategoryTheory

-- These proved equations hide large construction bodies from kernel comparisons.
-- The chosen value is specified by equality with the explicit construction.
private theorem exists_eq_value {α : Sort w} (a : α) : ∃ b : α, b = a := ⟨a, rfl⟩

private noncomputable def fixedValue {α : Sort w} (a : α) : α :=
  Classical.choose (exists_eq_value a)

private theorem fixedValue_eq {α : Sort w} (a : α) : fixedValue a = a :=
  Classical.choose_spec (exists_eq_value a)

private instance overBinaryProduct {S : Scheme.{u}} (T U : Over S) :
    Limits.HasBinaryProduct T U := inferInstance

private instance overPullback {S : Scheme.{u}} {T U V : Over S}
    (f : T ⟶ V) (g : U ⟶ V) : Limits.HasPullback f g := inferInstance

attribute [local implicit_reducible] discreteModuli discreteModuliMap
  moduliTwoFiberProduct BasedCategory.ofFunctor


private noncomputable def pullObj {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) {U : Over S} (q : U ⟶ T) : F.obj :=
  have := h.1
  Functor.IsPreFibered.pullbackObj x.property q

private noncomputable def pullArrow {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) {U : Over S} (q : U ⟶ T) :
    pullObj F h x q ⟶ x.val :=
  have := h.1
  Functor.IsPreFibered.pullbackMap x.property q

private instance pullArrow_lift {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) {U : Over S} (q : U ⟶ T) :
    F.p.IsHomLift q (pullArrow F h x q) := by
  have := h.1
  exact inferInstanceAs
    (F.p.IsHomLift q (Functor.IsPreFibered.pullbackMap x.property q))

private instance pullArrow_cartesian {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) {U : Over S} (q : U ⟶ T) :
    F.p.IsStronglyCartesian q (pullArrow F h x q) := by
  have := h.1
  exact inferInstanceAs
    (F.p.IsStronglyCartesian q (Functor.IsPreFibered.pullbackMap x.property q))

private noncomputable def pullTransition {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) {U V : Over S}
    {q : U ⟶ T} {r : V ⟶ T} (f : U ⟶ V) (hf : q = f ≫ r) :
    pullObj F h x q ⟶ pullObj F h x r :=
  Functor.IsStronglyCartesian.map F.p r (pullArrow F h x r) hf
    (pullArrow F h x q)

private instance pullTransition_lift {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) {U V : Over S}
    {q : U ⟶ T} {r : V ⟶ T} (f : U ⟶ V) (hf : q = f ≫ r) :
    F.p.IsHomLift f (pullTransition F h x f hf) :=
  Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _

private theorem pullTransition_fac {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) {U V : Over S}
    {q : U ⟶ T} {r : V ⟶ T} (f : U ⟶ V) (hf : q = f ≫ r) :
    pullTransition F h x f hf ≫ pullArrow F h x r = pullArrow F h x q :=
  Functor.IsStronglyCartesian.fac _ _ _ _ _

private theorem pullObj_base {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) {U : Over S} (q : U ⟶ T) :
    F.p.obj (pullObj F h x q) = U :=
  IsHomLift.domain_eq F.p q (pullArrow F h x q)

private theorem pullTransition_id {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T U : Over S} (x : Functor.Fiber F.p T) (q : U ⟶ T)
    (hq : q = (𝟙 U) ≫ q) : pullTransition F h x (𝟙 U) hq = 𝟙 _ := by
  have : F.p.IsHomLift (𝟙 U) (𝟙 (pullObj F h x q)) :=
    IsHomLift.id (pullObj_base F h x q)
  apply Functor.IsStronglyCartesian.ext F.p q (pullArrow F h x q) (𝟙 U)
  simp only [pullTransition_fac, Category.id_comp]

private theorem pullTransition_comp {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T U V W : Over S} (x : Functor.Fiber F.p T)
    {q : U ⟶ T} {r : V ⟶ T} {s : W ⟶ T} (f : U ⟶ V) (g : V ⟶ W)
    (hf : q = f ≫ r) (hg : r = g ≫ s) (hfg : q = (f ≫ g) ≫ s) :
    pullTransition F h x (f ≫ g) hfg =
      pullTransition F h x f hf ≫ pullTransition F h x g hg := by
  apply Functor.IsStronglyCartesian.ext F.p s (pullArrow F h x s) (f ≫ g)
  simp only [Category.assoc, pullTransition_fac]

private noncomputable def objectFunctor {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) :
    (discreteModuli (yoneda.obj T)).obj ⥤ F.obj where
  obj A := pullObj F h x (yoneda.preimage A.hom)
  map {A B} f := pullTransition F h x f.left (by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, Functor.map_preimage] using
      (CostructuredArrow.w f).symm)
  map_id A := pullTransition_id F h x _ _
  map_comp f g := pullTransition_comp F h x f.left g.left _ _ _

private noncomputable def objectSection {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T : Over S} (x : Functor.Fiber F.p T) :
    BasedFunctor (discreteModuli (yoneda.obj T)) F where
  toFunctor := objectFunctor F h x
  w := by
    let e (A : (discreteModuli (yoneda.obj T)).obj) :
        F.p.obj ((objectFunctor F h x).obj A) = A.left := pullObj_base F h x _
    exact Functor.ext_of_iso
      (NatIso.ofComponents (fun A ↦ eqToIso (e A)) (fun f ↦ by
        have : F.p.IsHomLift f.left ((objectFunctor F h x).map f) :=
          pullTransition_lift F h x f.left (by
            apply yoneda.map_injective
            simpa only [Functor.map_comp, Functor.map_preimage] using
              (CostructuredArrow.w f).symm)
        exact (IsHomLift.commSq F.p f.left ((objectFunctor F h x).map f)).w))
      e (fun _ ↦ rfl)

private theorem stronglyCartesian_lift {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T U : Over S} {x y : F.obj} (q : U ⟶ T) (a : x ⟶ y)
    (ha : F.p.IsHomLift q a) : F.p.IsStronglyCartesian q a := by
  have := h.2 a
  cases ha
  infer_instance

private noncomputable def comparisonIso {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T U : Over S} (x : Functor.Fiber F.p T) (q : U ⟶ T)
    (xU : Functor.Fiber F.p U) (a : xU.val ⟶ x.val)
    (ha : F.p.IsHomLift q a) :
    xU ≅ ⟨pullObj F h x q, pullObj_base F h x q⟩ := by
  have := ha
  have := stronglyCartesian_lift F h q a ha
  let e := Functor.IsCartesian.domainUniqueUpToIso F.p q (pullArrow F h x q) a
  refine ⟨⟨e.hom, inferInstance⟩, ⟨e.inv, inferInstance⟩, ?_, ?_⟩
  · apply Subtype.ext
    exact e.hom_inv_id
  · apply Subtype.ext
    exact e.inv_hom_id

private theorem comparisonIso_fac {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T U : Over S} (x : Functor.Fiber F.p T) (q : U ⟶ T)
    (xU : Functor.Fiber F.p U) (a : xU.val ⟶ x.val)
    (ha : F.p.IsHomLift q a) :
    (comparisonIso F h x q xU a ha).hom.val ≫ pullArrow F h x q = a := by
  have := ha
  have := stronglyCartesian_lift F h q a ha
  exact Functor.IsCartesian.fac F.p q (pullArrow F h x q) a

private theorem discreteTwoIso_eq {S : Scheme.{u}}
    {A : BasedCategory.{v, w} (Over S)} {P : (Over S)ᵒᵖ ⥤ Type u}
    {f g : BasedFunctor A (discreteModuli P)} (e : ModuliTwoIso f g) : f = g := by
  have he (x : A.obj) : (f.obj x).left = (g.obj x).left :=
    (f.w_obj x).trans (g.w_obj x).symm
  have hm (x : A.obj) : (e.val.hom.app x).left = eqToHom (he x) := by
    have hl := e.property x
    have : (discreteModuli P).p.IsHomLift
        (𝟙 ((discreteModuli P).p.obj (f.obj x))) (e.val.hom.app x) := by
      change (discreteModuli P).p.IsHomLift (𝟙 (f.obj x).left) _
      rw [show (f.obj x).left = A.p.obj x from f.w_obj x]
      exact hl
    simpa only [discreteModuli, BasedCategory.ofFunctor, CostructuredArrow.proj_map,
      Category.comp_id, Category.id_comp, eqToHom_trans] using
      (IsHomLift.fac' (discreteModuli P).p (𝟙 ((discreteModuli P).p.obj (f.obj x)))
        (e.val.hom.app x))
  have ho (x : A.obj) : f.obj x = g.obj x := by
    apply CostructuredArrow.obj_ext _ _ (he x)
    rw [← hm]
    exact CostructuredArrow.w (e.val.hom.app x)
  have hf : f.toFunctor = g.toFunctor := by
    exact Functor.ext_of_iso e.val ho (fun x ↦ by
      apply CostructuredArrow.ext
      change (e.val.hom.app x).left = (eqToHom (ho x)).left
      rw [CostructuredArrow.eqToHom_left]
      exact hm x)
  cases f
  cases g
  cases hf
  rfl

private noncomputable def normalizedComparison {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (e : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct a b))
    (e₁ : ModuliTwoIso (e.comp (moduliTwoFiberFst a b))
      (discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)))
    (e₂ : ModuliTwoIso (e.comp (moduliTwoFiberSnd a b))
      (discreteModuliMap (p ≫ yoneda.map Limits.prod.snd))) :
    ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor := by
  have h₁ := discreteTwoIso_eq e₁
  have h₂ := discreteTwoIso_eq e₂
  let n := Functor.whiskerLeft e.toFunctor
    (Functor.whiskerLeft (ObjectProperty.ι _) (Comma.natTrans a.toFunctor b.toFunctor))
  have (x : (discreteModuli Z.obj.obj).obj) : IsIso (n.app x) :=
    (e.obj x).property.1
  have : IsIso n := NatIso.isIso_of_isIso_app n
  let α : (e.comp (moduliTwoFiberFst a b)).toFunctor ⋙ a.toFunctor ≅
      (e.comp (moduliTwoFiberSnd a b)).toFunctor ⋙ b.toFunctor := asIso n
  let l := congrArg (fun k : BasedFunctor (discreteModuli Z.obj.obj)
      (discreteModuli (yoneda.obj T)) ↦ k.toFunctor ⋙ a.toFunctor) h₁
  let r := congrArg (fun k : BasedFunctor (discreteModuli Z.obj.obj)
      (discreteModuli (yoneda.obj U)) ↦ k.toFunctor ⋙ b.toFunctor) h₂
  exact (eqToIso l).symm ≪≫ α ≪≫ eqToIso r

private theorem normalizedComparison_vertical {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (e : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct a b))
    (e₁ : ModuliTwoIso (e.comp (moduliTwoFiberFst a b))
      (discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)))
    (e₂ : ModuliTwoIso (e.comp (moduliTwoFiberSnd a b))
      (discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)))
    (A : (discreteModuli Z.obj.obj).obj) :
    F.p.IsHomLift (𝟙 A.left) ((normalizedComparison F a b Z p e e₁ e₂).hom.app A) := by
  have h₁ := discreteTwoIso_eq e₁
  have h₂ := discreteTwoIso_eq e₂
  have hraw : F.p.IsHomLift (𝟙 A.left) (e.obj A).obj.hom := by
    have hr := (e.obj A).property.2
    change F.p.IsHomLift (𝟙 ((moduliTwoFiberProduct a b).p.obj (e.obj A))) _ at hr
    rw [e.w_obj] at hr
    exact hr
  dsimp only [normalizedComparison, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    eqToIso.hom, NatTrans.comp_app, eqToHom_app, asIso_hom]
  simp only [eqToHom_app, IsHomLift.comp_eqToHom_lift_iff,
    IsHomLift.eqToHom_comp_lift_iff]
  exact hraw

private noncomputable def normalizedFunctor {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A)) :
    (discreteModuli Z.obj.obj).obj ⥤ (moduliTwoFiberProduct a b).obj where
  obj A := ⟨⟨(discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).obj A,
    (discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).obj A,
    n.hom.app A⟩,
    ⟨inferInstance, hn A⟩⟩
  map f := ObjectProperty.homMk
    { left := (discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).map f
      right := (discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).map f
      w := n.hom.naturality f }
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> rfl

private noncomputable def normalizedFunctorIso {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (e : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct a b))
    (e₁ : ModuliTwoIso (e.comp (moduliTwoFiberFst a b))
      (discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)))
    (e₂ : ModuliTwoIso (e.comp (moduliTwoFiberSnd a b))
      (discreteModuliMap (p ≫ yoneda.map Limits.prod.snd))) :
    e.toFunctor ≅ normalizedFunctor F a b Z p (normalizedComparison F a b Z p e e₁ e₂)
      (normalizedComparison_vertical F a b Z p e e₁ e₂) := by
  let h₁ := discreteTwoIso_eq e₁
  let h₂ := discreteTwoIso_eq e₂
  refine NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _
    (Comma.isoMk (eqToIso (congrArg (fun k ↦ k.obj A) h₁))
      (eqToIso (congrArg (fun k ↦ k.obj A) h₂)) ?_)) ?_
  · change a.map (eqToHom (congrArg (fun k ↦ k.obj A) h₁)) ≫
        (normalizedComparison F a b Z p e e₁ e₂).hom.app A =
      (e.obj A).obj.hom ≫ b.map (eqToHom (congrArg (fun k ↦ k.obj A) h₂))
    simp only [normalizedComparison, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
      eqToIso.hom, NatTrans.comp_app, eqToHom_app, asIso_hom, eqToHom_map]
    rw [← Category.assoc, eqToHom_trans]
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  · intro A B f
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · change (e.comp (moduliTwoFiberFst a b)).map f ≫
        eqToHom (congrArg (fun k ↦ k.obj B) h₁) =
        eqToHom (congrArg (fun k ↦ k.obj A) h₁) ≫
          (discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).map f
      simpa only [eqToHom_app] using
        (eqToHom (congrArg BasedFunctor.toFunctor h₁)).naturality f
    · change (e.comp (moduliTwoFiberSnd a b)).map f ≫
        eqToHom (congrArg (fun k ↦ k.obj B) h₂) =
        eqToHom (congrArg (fun k ↦ k.obj A) h₂) ≫
          (discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).map f
      simpa only [eqToHom_app] using
        (eqToHom (congrArg BasedFunctor.toFunctor h₂)).naturality f

private theorem projection_section_eq {S : Scheme.{u}} {T U V : Over S}
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    (discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).obj
        (CostructuredArrow.mk z) = CostructuredArrow.mk (yoneda.map q) ∧
      (discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).obj
        (CostructuredArrow.mk z) = CostructuredArrow.mk (yoneda.map r) := by
  constructor
  · change CostructuredArrow.mk (z ≫ (p ≫ yoneda.map Limits.prod.fst)) = _
    apply congrArg (fun t : yoneda.obj V ⟶ yoneda.obj T ↦ CostructuredArrow.mk t)
    rw [← Category.assoc, hz, ← Functor.map_comp, Limits.prod.lift_fst]
  · change CostructuredArrow.mk (z ≫ (p ≫ yoneda.map Limits.prod.snd)) = _
    apply congrArg (fun t : yoneda.obj V ⟶ yoneda.obj U ↦ CostructuredArrow.mk t)
    rw [← Category.assoc, hz, ← Functor.map_comp, Limits.prod.lift_snd]

private noncomputable def rawSectionComparison {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (_hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)) :=
  let h := projection_section_eq Z p q r z hz
  (a.toFunctor.mapIso (eqToIso h.1)).symm ≪≫
    n.app (CostructuredArrow.mk z) ≪≫
    b.toFunctor.mapIso (eqToIso h.2)

private noncomputable def sectionComparison {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)) :=
  fixedValue (rawSectionComparison F a b Z p n hn q r z hz)

private theorem sectionComparison_def {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    sectionComparison F a b Z p n hn q r z hz =
      rawSectionComparison F a b Z p n hn q r z hz := fixedValue_eq _

private theorem sectionComparison_vertical {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    F.p.IsHomLift (𝟙 V) (sectionComparison F a b Z p n hn q r z hz).hom := by
  rw [sectionComparison_def]
  dsimp only [rawSectionComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, eqToIso.hom, eqToIso.inv]
  simp only [eqToHom_map, IsHomLift.comp_eqToHom_lift_iff,
    IsHomLift.eqToHom_comp_lift_iff]
  simpa only [Iso.app_hom, BasedFunctor.comp_toFunctor, Functor.comp_obj,
    CostructuredArrow.mk_left] using
    hn (CostructuredArrow.mk z)

private noncomputable def commaSection {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (q : V ⟶ T) (r : V ⟶ U)
    (γ : a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)))
    (hγ : F.p.IsHomLift (𝟙 V) γ.hom) : (moduliTwoFiberProduct a b).obj :=
  ⟨⟨CostructuredArrow.mk (yoneda.map q), CostructuredArrow.mk (yoneda.map r), γ.hom⟩,
    ⟨inferInstance, hγ⟩⟩

private noncomputable def rawSectionComparisonIso {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    (normalizedFunctor F a b Z p n hn).obj (CostructuredArrow.mk z) ≅
      commaSection F a b q r (sectionComparison F a b Z p n hn q r z hz)
        (sectionComparison_vertical F a b Z p n hn q r z hz) := by
  let h := projection_section_eq Z p q r z hz
  refine ObjectProperty.isoMk _ (Comma.isoMk (eqToIso h.1) (eqToIso h.2) ?_)
  change a.map (eqToHom h.1) ≫
      (sectionComparison F a b Z p n hn q r z hz).hom =
    n.hom.app _ ≫ b.map (eqToHom h.2)
  simp only [sectionComparison_def, rawSectionComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom,
    Functor.mapIso_inv, eqToIso.hom, eqToIso.inv, eqToHom_map]
  rw [← Category.assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp, Iso.app_hom]

private noncomputable def sectionComparisonIso {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    (normalizedFunctor F a b Z p n hn).obj (CostructuredArrow.mk z) ≅
      commaSection F a b q r (sectionComparison F a b Z p n hn q r z hz)
        (sectionComparison_vertical F a b Z p n hn q r z hz) :=
  fixedValue (rawSectionComparisonIso F a b Z p n hn q r z hz)

private theorem sectionComparisonIso_eq {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    sectionComparisonIso F a b Z p n hn q r z hz =
      rawSectionComparisonIso F a b Z p n hn q r z hz := fixedValue_eq _

private theorem sectionComparisonIso_hom_left {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    (sectionComparisonIso F a b Z p n hn q r z hz).hom.hom.left.left =
      𝟙 V := by
  rw [sectionComparisonIso_eq]
  change (eqToHom (projection_section_eq Z p q r z hz).1).left = 𝟙 V
  exact CostructuredArrow.eqToHom_left _

private theorem sectionComparisonIso_inv_left {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    (sectionComparisonIso F a b Z p n hn q r z hz).inv.hom.left.left =
      𝟙 V := by
  rw [sectionComparisonIso_eq]
  change (eqToHom (projection_section_eq Z p q r z hz).1.symm).left = 𝟙 V
  exact CostructuredArrow.eqToHom_left _

private theorem twoFiber_comp_left {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {T U : Over S}
    {a : BasedFunctor (discreteModuli (yoneda.obj T)) F}
    {b : BasedFunctor (discreteModuli (yoneda.obj U)) F}
    {A B C : (moduliTwoFiberProduct a b).obj} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.left.left = f.hom.left.left ≫ g.hom.left.left := rfl

private theorem functor_map_heq {C : Type u} {D : Type w}
    [Category C] [Category D] {L R : C ⥤ D} (h : L = R)
    {X Y : C} (f : X ⟶ Y) : HEq (L.map f) (R.map f) := by
  cases h
  rfl

private theorem twoFiber_bases {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {T U : Over S}
    {a : BasedFunctor (discreteModuli (yoneda.obj T)) F}
    {b : BasedFunctor (discreteModuli (yoneda.obj U)) F}
    {A B : (moduliTwoFiberProduct a b).obj} (f : A ⟶ B) :
    HEq f.hom.right.left f.hom.left.left := by
  exact functor_map_heq (moduliTwoFiberSnd_projection a b) f

private theorem twoFiber_eqToHom_base {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {T U : Over S}
    {a : BasedFunctor (discreteModuli (yoneda.obj T)) F}
    {b : BasedFunctor (discreteModuli (yoneda.obj U)) F}
    {A B : (moduliTwoFiberProduct a b).obj} (h : A = B) :
    (eqToHom h).hom.left.left = eqToHom (congrArg (fun X ↦ X.obj.left.left) h) := by
  cases h
  rfl

private theorem discreteSections_equal_of_equivalence {S : Scheme.{u}}
    (P : (Over S)ᵒᵖ ⥤ Type u) {D : Type w} [Category.{v} D]
    (N : (discreteModuli P).obj ⥤ D) [N.Full] [N.Faithful]
    (base : D ⥤ Over S)
    (hmap : ∀ {A B} (f : A ⟶ B), HEq (base.map (N.map f)) f.left)
    {V : Over S} (z z' : yoneda.obj V ⟶ P)
    (l : N.obj (CostructuredArrow.mk z) ⟶ N.obj (CostructuredArrow.mk z'))
    (hl : HEq (base.map l) (𝟙 V)) : z = z' := by
  let k := N.preimage l
  have hk : k.left = 𝟙 V := by
    apply eq_of_heq
    apply (hmap k).symm.trans
    rw [N.map_preimage]
    exact hl
  have hw := CostructuredArrow.w k
  change yoneda.map k.left ≫ z' = z at hw
  rw [hk] at hw
  change (𝟙 (yoneda.obj V)) ≫ z' = z at hw
  exact hw.symm.trans (Category.id_comp z')

private theorem normalizedFunctor_map_left {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    {A B : (discreteModuli Z.obj.obj).obj} (k : A ⟶ B) :
    ((normalizedFunctor F a b Z p n hn).map k).hom.left.left = k.left := rfl

private theorem discreteSections_equal_of_comma_isos {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) {T U V : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (P : (Over S)ᵒᵖ ⥤ Type u)
    (N : (discreteModuli P).obj ⥤ (moduliTwoFiberProduct a b).obj)
    [N.Full] [N.Faithful]
    (hobj : ∀ A, (N.obj A).obj.left.left = A.left)
    (hmap : ∀ {A B} (f : A ⟶ B), HEq (N.map f).hom.left.left f.left)
    (q : V ⟶ T) (r : V ⟶ U) (z z' : yoneda.obj V ⟶ P)
    (γ δ : a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)))
    (hγ : F.p.IsHomLift (𝟙 V) γ.hom) (hδ : F.p.IsHomLift (𝟙 V) δ.hom)
    (j : N.obj (CostructuredArrow.mk z) ≅ commaSection F a b q r γ hγ)
    (j' : N.obj (CostructuredArrow.mk z') ≅ commaSection F a b q r δ hδ)
    (hj : HEq j.hom.hom.left.left (𝟙 V))
    (hj' : HEq j'.inv.hom.left.left (𝟙 V))
    (h : γ = δ) : z = z' := by
  have hC : commaSection F a b q r γ hγ = commaSection F a b q r δ hδ := by
    cases h
    rfl
  let l := j.hom ≫ eqToHom hC ≫ j'.inv
  let base := (moduliTwoFiberFst a b).toFunctor ⋙ (discreteModuli (yoneda.obj T)).p
  apply discreteSections_equal_of_equivalence P N base (fun f ↦ hmap f) z z' l
  change HEq l.hom.left.left (𝟙 V)
  dsimp only [l]
  rw [twoFiber_comp_left, twoFiber_comp_left]
  have hm : (eqToHom hC).hom.left.left = 𝟙 V := by
    rw [twoFiber_eqToHom_base]
    rfl
  exact (heq_comp (hobj _) rfl (hobj _ ) hj
    (heq_comp rfl rfl (hobj _) (heq_of_eq hm) hj')).trans
      (heq_of_eq (show (𝟙 V) ≫ (𝟙 V) ≫ (𝟙 V) = 𝟙 V from
        (Category.id_comp _).trans (Category.id_comp _)))

private theorem sectionComparison_injective {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (he : (normalizedFunctor F a b Z p n hn).IsEquivalence)
    (q : V ⟶ T) (r : V ⟶ U) (z z' : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r))
    (hz' : z' ≫ p = yoneda.map (Limits.prod.lift q r))
    (hγ : sectionComparison F a b Z p n hn q r z hz =
      sectionComparison F a b Z p n hn q r z' hz') : z = z' := by
  have := he
  exact discreteSections_equal_of_comma_isos F a b Z.obj.obj
    (normalizedFunctor F a b Z p n hn) (fun _ ↦ rfl) (fun _ ↦ HEq.rfl)
    q r z z' _ _ _ _
    (sectionComparisonIso F a b Z p n hn q r z hz)
    (sectionComparisonIso F a b Z p n hn q r z' hz')
    (heq_of_eq (sectionComparisonIso_hom_left F a b Z p n hn q r z hz))
    (heq_of_eq (sectionComparisonIso_inv_left F a b Z p n hn q r z' hz')) hγ

private theorem commaSection_hom_eq {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (q : V ⟶ T) (r : V ⟶ U)
    (γ δ : a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)))
    (hγ : F.p.IsHomLift (𝟙 V) γ.hom) (hδ : F.p.IsHomLift (𝟙 V) δ.hom)
    (f : commaSection F a b q r γ hγ ⟶ commaSection F a b q r δ hδ)
    (hf : f.hom.left.left = 𝟙 V) : γ = δ := by
  have hr : f.hom.right.left = 𝟙 V := by
    have hh := Functor.congr_hom (moduliTwoFiberSnd_projection a b) f
    change f.hom.right.left = f.hom.left.left at hh
    exact hh.trans hf
  have hl : f.hom.left = 𝟙 _ := CostructuredArrow.ext _ _ hf
  have hr' : f.hom.right = 𝟙 _ := CostructuredArrow.ext _ _ hr
  apply Iso.ext
  have hh := f.hom.w
  change a.map f.hom.left ≫ δ.hom = γ.hom ≫ b.map f.hom.right at hh
  rw [hl, hr'] at hh
  change a.map (𝟙 (CostructuredArrow.mk (yoneda.map q))) ≫ δ.hom =
    γ.hom ≫ b.map (𝟙 (CostructuredArrow.mk (yoneda.map r))) at hh
  rw [a.toFunctor.map_id, b.toFunctor.map_id, Category.id_comp, Category.comp_id] at hh
  exact hh.symm

private theorem sectionComparison_equal_of_lift {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U)
    (γ : a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)))
    (hγ : F.p.IsHomLift (𝟙 V) γ.hom)
    (A : (discreteModuli Z.obj.obj).obj)
    (j : (normalizedFunctor F a b Z p n hn).obj A ≅ commaSection F a b q r γ hγ)
    (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r))
    (k : CostructuredArrow.mk z ⟶ A) (hk : k.left = j.inv.hom.left.left) :
    sectionComparison F a b Z p n hn q r z hz = γ := by
  let N := normalizedFunctor F a b Z p n hn
  let l := (sectionComparisonIso F a b Z p n hn q r z hz).inv ≫ N.map k ≫ j.hom
  apply commaSection_hom_eq F a b q r _ γ _ hγ l
  dsimp only [l]
  rw [twoFiber_comp_left, twoFiber_comp_left, sectionComparisonIso_inv_left,
    normalizedFunctor_map_left, hk]
  change (𝟙 V) ≫ (j.inv.hom.left.left ≫ j.hom.hom.left.left) = 𝟙 V
  have hj := congrArg (fun f ↦ f.hom.left.left) j.inv_hom_id
  exact (Category.id_comp _).trans hj

private theorem sectionComparison_surjective_of_iso {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U)
    (γ : a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)))
    (hγ : F.p.IsHomLift (𝟙 V) γ.hom)
    (A : (discreteModuli Z.obj.obj).obj)
    (j : (normalizedFunctor F a b Z p n hn).obj A ≅ commaSection F a b q r γ hγ) :
    ∃ (z : yoneda.obj V ⟶ Z.obj.obj)
      (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)),
      sectionComparison F a b Z p n hn q r z hz = γ := by
  let N := normalizedFunctor F a b Z p n hn
  let z : yoneda.obj V ⟶ Z.obj.obj := yoneda.map j.inv.hom.left.left ≫ A.hom
  have hbase : j.inv.hom.right.left = j.inv.hom.left.left := eq_of_heq (twoFiber_bases j.inv)
  have hz : z ≫ p = yoneda.map (Limits.prod.lift q r) := by
    let t := yoneda.preimage (z ≫ p)
    rw [← show yoneda.map t = z ≫ p from yoneda.map_preimage _]
    apply congrArg yoneda.map
    apply Limits.prod.hom_ext
    · apply yoneda.map_injective
      have hh := CostructuredArrow.w j.inv.hom.left
      change yoneda.map j.inv.hom.left.left ≫
        (A.hom ≫ (p ≫ yoneda.map Limits.prod.fst)) = yoneda.map q at hh
      simpa only [Functor.map_comp, Functor.map_preimage, Limits.prod.lift_fst,
        t, z, Category.assoc] using hh
    · apply yoneda.map_injective
      have hh := CostructuredArrow.w j.inv.hom.right
      change yoneda.map j.inv.hom.right.left ≫
        (A.hom ≫ (p ≫ yoneda.map Limits.prod.snd)) = yoneda.map r at hh
      rw [hbase] at hh
      simpa only [Functor.map_comp, Functor.map_preimage, Limits.prod.lift_snd,
        t, z, Category.assoc] using hh
  let k : CostructuredArrow.mk z ⟶ A := CostructuredArrow.homMk
    j.inv.hom.left.left rfl
  exact ⟨z, hz, sectionComparison_equal_of_lift F a b Z p n hn q r γ hγ A j z hz k rfl⟩

private theorem sectionComparison_surjective {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (he : (normalizedFunctor F a b Z p n hn).IsEquivalence)
    (q : V ⟶ T) (r : V ⟶ U)
    (γ : a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)))
    (hγ : F.p.IsHomLift (𝟙 V) γ.hom)
 :
    ∃ (z : yoneda.obj V ⟶ Z.obj.obj)
      (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)),
      sectionComparison F a b Z p n hn q r z hz = γ := by
  have := he
  let N := normalizedFunctor F a b Z p n hn
  exact sectionComparison_surjective_of_iso F a b Z p n hn q r γ hγ
    (N.objPreimage _) (N.objObjPreimageIso _)

@[implicit_reducible] private def testRestriction {S : Scheme.{u}} {T V V' : Over S}
    (q : V ⟶ T) (f : V' ⟶ V) :
    CostructuredArrow.mk (yoneda.map (f ≫ q)) ⟶
      CostructuredArrow.mk (yoneda.map q) :=
  CostructuredArrow.homMk f (yoneda.map_comp f q).symm

private theorem commaSection_naturality {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) {T U V V' : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (q : V ⟶ T) (r : V ⟶ U) (f : V' ⟶ V)
    (γ : a.obj (CostructuredArrow.mk (yoneda.map q)) ≅
      b.obj (CostructuredArrow.mk (yoneda.map r)))
    (γ' : a.obj (CostructuredArrow.mk (yoneda.map (f ≫ q))) ≅
      b.obj (CostructuredArrow.mk (yoneda.map (f ≫ r))))
    (hγ : F.p.IsHomLift (𝟙 V) γ.hom) (hγ' : F.p.IsHomLift (𝟙 V') γ'.hom)
    (l : commaSection F a b (f ≫ q) (f ≫ r) γ' hγ' ⟶
      commaSection F a b q r γ hγ)
    (hl : l.hom.left = testRestriction q f)
    (hr : l.hom.right = testRestriction r f) :
    γ'.hom ≫ b.map (testRestriction r f) = a.map (testRestriction q f) ≫ γ.hom := by
  have hh := l.hom.w.symm
  change γ'.hom ≫ b.map l.hom.right = a.map l.hom.left ≫ γ.hom at hh
  rw [hl, hr] at hh
  exact hh

private theorem sectionComparison_naturality {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V V' : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (f : V' ⟶ V)
    (z : yoneda.obj V ⟶ Z.obj.obj) (z' : yoneda.obj V' ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r))
    (hz' : z' ≫ p = yoneda.map (Limits.prod.lift (f ≫ q) (f ≫ r)))
    (hf : yoneda.map f ≫ z = z') :
    (sectionComparison F a b Z p n hn (f ≫ q) (f ≫ r) z' hz').hom ≫
        b.map (testRestriction r f) =
      a.map (testRestriction q f) ≫
        (sectionComparison F a b Z p n hn q r z hz).hom := by
  let N := normalizedFunctor F a b Z p n hn
  let k : CostructuredArrow.mk z' ⟶ CostructuredArrow.mk z :=
    CostructuredArrow.homMk f hf
  let j := sectionComparisonIso F a b Z p n hn q r z hz
  let j' := sectionComparisonIso F a b Z p n hn (f ≫ q) (f ≫ r) z' hz'
  let l := j'.inv ≫ N.map k ≫ j.hom
  have hl : l.hom.left = testRestriction q f := by
    apply CostructuredArrow.ext
    dsimp only [l]
    rw [twoFiber_comp_left, twoFiber_comp_left]
    rw [sectionComparisonIso_inv_left, sectionComparisonIso_hom_left,
      normalizedFunctor_map_left]
    exact Category.id_comp (f ≫ 𝟙 V) |>.trans (Category.comp_id f)
  have hr : l.hom.right = testRestriction r f := by
    apply CostructuredArrow.ext
    exact (eq_of_heq (twoFiber_bases l)).trans (congrArg (fun k ↦ k.left) hl)
  exact commaSection_naturality F a b q r f _ _ _ _ l hl hr

private theorem property_of_scheme_test {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {G H : (Over S)ᵒᵖ ⥤ Type u} {f : G ⟶ H}
    (hf : AlgebraicSpace.IsRepresentableWith (P.inverseImage (Over.forget S)) f)
    {T U : Over S} {a : yoneda.obj T ⟶ H} {p : U ⟶ T}
    {q : yoneda.obj U ⟶ G} (h : IsPullback q (yoneda.map p) f a) : P p.left := by
  obtain ⟨V, r, b, hb, hr⟩ := hf T a
  let e : U ≅ V := yoneda.preimageIso (h.isoIsPullback _ _ hb)
  have he : e.hom ≫ r = p := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, e, Functor.preimageIso_hom, Functor.map_preimage] using
      h.isoIsPullback_hom_snd _ _ hb
  have hP : P (e.hom.left ≫ r.left) :=
    MorphismProperty.RespectsIso.precomp P e.hom.left r.left hr
  simpa only [← Over.comp_left, he] using hP

private theorem space_unramified_pullback {S : Scheme.{u}}
    (Z I : AlgebraicSpace S) {T T' : Over S} (p : Z.obj.obj ⟶ yoneda.obj T)
    (pI : I.obj.obj ⟶ yoneda.obj T') (j : I.obj.obj ⟶ Z.obj.obj) (g : T' ⟶ T)
    (sq : IsPullback j pI p (yoneda.map g)) (hp : SpaceMapIsUnramified Z T p) :
    SpaceMapIsUnramified I T' pI := by
  obtain ⟨A, a, hae, has⟩ := Z.property.2
  let r : A ⟶ T := yoneda.preimage (a ≫ p)
  have hr : yoneda.map r = a ≫ p := yoneda.map_preimage _
  let R := Limits.pullback r g
  let d : R ⟶ T' := Limits.pullback.snd r g
  let c : yoneda.obj R ⟶ I.obj.obj := sq.lift
    (yoneda.map (Limits.pullback.fst r g) ≫ a) (yoneda.map d) (by
      rw [Category.assoc, ← hr, ← Functor.map_comp, Limits.pullback.condition,
        Functor.map_comp])
  have csq : IsPullback (yoneda.map (Limits.pullback.fst r g)) c a j := by
    have houter : IsPullback (yoneda.map (Limits.pullback.fst r g))
        (yoneda.map d) (a ≫ p) (yoneda.map g) := by
      rw [← hr]
      exact yoneda.map_isPullback (IsPullback.of_hasPullback r g)
    apply IsPullback.of_right (h₁₂ := pI) (h₂₂ := p)
      (h₁₁ := c) (v₁₁ := yoneda.map (Limits.pullback.fst r g))
      (v₁₂ := j) (v₁₃ := yoneda.map g) ?_ (sq.lift_fst _ _ _) sq.flip |>.flip
    simpa only [c, IsPullback.lift_snd] using houter.flip
  have hc : AlgebraicSpace.IsEtale c :=
    AlgebraicSpace.representableWith_baseChange _ csq hae
  have hcs : AlgebraicSpace.IsSurjective c :=
    AlgebraicSpace.representableWith_baseChange _ csq has
  have hd : IsUnramified d.left := by
    have hh := hp A a hae
    change IsUnramified r.left at hh
    have : LocallyOfFiniteType r.left := hh.1
    have : IsOpenImmersion (Limits.pullback.diagonal r.left) := hh.2
    have hu : FormallyUnramified r.left := inferInstance
    have hsq := (IsPullback.of_hasPullback r g).map (Over.forget S)
    have : LocallyOfFiniteType d.left :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hsq hh.1
    have : FormallyUnramified d.left :=
      MorphismProperty.of_isPullback (P := @FormallyUnramified) hsq hu
    exact ⟨inferInstance, inferInstance⟩
  intro V b hb
  obtain ⟨E, e, t, esq, hes⟩ := hcs V b
  have hee : Etale e.left := property_of_scheme_test @Etale hc esq
  let t' : E ⟶ R := yoneda.preimage t
  have ht : yoneda.map t' = t := yoneda.map_preimage _
  have hte : Etale t'.left := by
    apply property_of_scheme_test @Etale hb
    simpa only [ht] using esq.flip
  let f : V ⟶ T' := yoneda.preimage (b ≫ pI)
  have hcomm : e ≫ f = t' ≫ d := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, f, Functor.map_preimage, ht]
    rw [← Category.assoc, ← esq.w, Category.assoc, sq.lift_snd]
  have hecomp : IsUnramified (e.left ≫ f.left) := by
    rw [← Over.comp_left, hcomm, Over.comp_left]
    exact scheme_unramified_etale_locality.1 _ _ _ t'.left d.left hte hd
  apply (scheme_unramified_etale_locality.2.2 V.left T'.left f.left).mpr
  intro v
  have := hes
  obtain ⟨w, hw⟩ := e.left.surjective v
  exact ⟨E.left, T'.left, e.left, 𝟙 T'.left, w, e.left ≫ f.left,
    hee, inferInstance, hw, (Category.comp_id _).symm, hecomp⟩

@[implicit_reducible] private def sectionFiber {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) {T V : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj T)) F) (q : V ⟶ T) :
    Functor.Fiber F.p V := ⟨a.obj (CostructuredArrow.mk (yoneda.map q)), a.w_obj _⟩

private noncomputable def fiberSectionComparison {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (q : V ⟶ T) (r : V ⟶ U) (z : yoneda.obj V ⟶ Z.obj.obj)
    (hz : z ≫ p = yoneda.map (Limits.prod.lift q r)) :
    sectionFiber F a q ≅
      sectionFiber F b r := by
  let γ := sectionComparison F a b Z p n hn q r z hz
  have hγ := sectionComparison_vertical F a b Z p n hn q r z hz
  refine ⟨⟨γ.hom, hγ⟩, ⟨γ.inv, ?_⟩, ?_, ?_⟩
  · exact IsHomLift.lift_id_inv F.p V γ
  · apply Subtype.ext
    exact γ.hom_inv_id
  · apply Subtype.ext
    exact γ.inv_hom_id

private noncomputable def fiberSectionEquiv {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    {T U V : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (b : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T U))
    (n : ((discreteModuliMap (p ≫ yoneda.map Limits.prod.fst)).comp a).toFunctor ≅
      ((discreteModuliMap (p ≫ yoneda.map Limits.prod.snd)).comp b).toFunctor)
    (hn : ∀ A, F.p.IsHomLift (𝟙 A.left) (n.hom.app A))
    (he : (normalizedFunctor F a b Z p n hn).IsEquivalence)
    (q : V ⟶ T) (r : V ⟶ U) :
    {z : yoneda.obj V ⟶ Z.obj.obj // z ≫ p = yoneda.map (Limits.prod.lift q r)} ≃
      (sectionFiber F a q ≅
        sectionFiber F b r) := by
  apply Equiv.ofBijective (fun z ↦ fiberSectionComparison F a b Z p n hn q r z.val z.property)
  constructor
  · intro z z' hh
    apply Subtype.ext
    apply sectionComparison_injective F a b Z p n hn he q r _ _ z.property z'.property
    apply Iso.ext
    exact congrArg (fun i ↦ i.hom.val) hh
  · intro δ
    let γ := Functor.Fiber.fiberInclusion.mapIso δ
    have hγ : F.p.IsHomLift (𝟙 V) γ.hom := δ.hom.property
    obtain ⟨z, hz, h⟩ := sectionComparison_surjective F a b Z p n hn he q r γ hγ
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Iso.ext
    apply Subtype.ext
    exact congrArg Iso.hom h

private noncomputable def diagonalSectionEquiv {S : Scheme.{u}}
    (Z I : AlgebraicSpace S) (T : Over S)
    (p : Z.obj.obj ⟶ yoneda.obj (Limits.prod T T))
    (pI : I.obj.obj ⟶ yoneda.obj T) (j : I.obj.obj ⟶ Z.obj.obj)
    (sq : IsPullback j pI p (yoneda.map (Limits.prod.lift (𝟙 T) (𝟙 T))))
    (V : Over S) (q : V ⟶ T) :
    {s : I.obj.obj.obj (op V) // pI.app (op V) s = q} ≃
      {z : yoneda.obj V ⟶ Z.obj.obj // z ≫ p = yoneda.map (Limits.prod.lift q q)} := by
  let f : {s : I.obj.obj.obj (op V) // pI.app (op V) s = q} →
      {z : yoneda.obj V ⟶ Z.obj.obj // z ≫ p = yoneda.map (Limits.prod.lift q q)} :=
    fun s ↦ ⟨yonedaEquiv.symm (j.app (op V) s.val), by
      apply yonedaEquiv.injective
      have hh := congrArg (fun α : I.obj.obj ⟶ yoneda.obj (Limits.prod T T) ↦
        α.app (op V) s.val) sq.w
      change p.app (op V) (j.app (op V) s.val) =
        pI.app (op V) s.val ≫ Limits.prod.lift (𝟙 T) (𝟙 T) at hh
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
      rw [s.property] at hh
      simpa only [Limits.prod.comp_lift, Category.comp_id] using hh⟩
  apply Equiv.ofBijective f
  constructor
  · intro s s' hs
    apply Subtype.ext
    apply Limits.Types.ext_of_isPullback (sq.app (op V))
    · exact yonedaEquiv.symm.injective (congrArg Subtype.val hs)
    · exact s.property.trans s'.property.symm
  · intro z
    have hz : p.app (op V) (yonedaEquiv z.val) =
        (yoneda.map (Limits.prod.lift (𝟙 T) (𝟙 T))).app (op V) q := by
      have hh := congrArg yonedaEquiv z.property
      change p.app (op V) (yonedaEquiv z.val) = Limits.prod.lift q q at hh
      change p.app (op V) (yonedaEquiv z.val) = q ≫ Limits.prod.lift (𝟙 T) (𝟙 T)
      simpa only [Limits.prod.comp_lift, Category.comp_id] using hh
    obtain ⟨s, hs, hq⟩ := Limits.Types.exists_of_isPullback (sq.app (op V))
      (yonedaEquiv z.val) q hz
    refine ⟨⟨s, hq⟩, Subtype.ext ?_⟩
    change yonedaEquiv.symm (j.app (op V) s) = z.val
    rw [hs, Equiv.symm_apply_apply]

private noncomputable def arbitraryComparison {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T V : Over S} (x : Functor.Fiber F.p T) (q : V ⟶ T)
    (xV : Functor.Fiber F.p V) (a : xV.val ⟶ x.val)
    (ha : F.p.IsHomLift q a) :
    xV ≅ (⟨(objectSection F h x).obj (CostructuredArrow.mk (yoneda.map q)),
      (objectSection F h x).w_obj _⟩ : Functor.Fiber F.p V) :=
  comparisonIso F h x (yoneda.preimage (yoneda.map q)) xV a (by
    simpa only [yoneda.preimage_map] using ha)

private theorem arbitraryComparison_naturality {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (h : IsFibredInGroupoids F)
    {T V V' : Over S} (x : Functor.Fiber F.p T) (q : V ⟶ T)
    (f : V' ⟶ V) (xV : Functor.Fiber F.p V) (xV' : Functor.Fiber F.p V')
    (a : xV.val ⟶ x.val) (a' : xV'.val ⟶ x.val)
    (ha : F.p.IsHomLift q a) (ha' : F.p.IsHomLift (f ≫ q) a')
    (c : xV'.val ⟶ xV.val) (hc : F.p.IsHomLift f c) (hca : c ≫ a = a') :
    (arbitraryComparison F h x (f ≫ q) xV' a' ha').hom.val ≫
        (objectSection F h x).map (testRestriction q f) =
      c ≫ (arbitraryComparison F h x q xV a ha).hom.val := by
  have := hc
  have := (arbitraryComparison F h x (f ≫ q) xV' a' ha').hom.property
  have := (arbitraryComparison F h x q xV a ha).hom.property
  have hm : F.p.IsHomLift f ((objectSection F h x).map (testRestriction q f)) := by
    have ht : (discreteModuli (yoneda.obj T)).p.IsHomLift f (testRestriction q f) :=
      IsHomLift.map (discreteModuli (yoneda.obj T)).p (testRestriction q f)
    exact BasedFunctor.preserves_isHomLift _ _ _
  have hfac (V : Over S) (q : V ⟶ T) (xV : Functor.Fiber F.p V)
      (a : xV.val ⟶ x.val) (ha : F.p.IsHomLift q a) :
      (arbitraryComparison F h x q xV a ha).hom.val ≫
        pullArrow F h x (yoneda.preimage (yoneda.map q)) = a := by
    exact comparisonIso_fac F h x (yoneda.preimage (yoneda.map q)) xV a _
  apply Functor.IsStronglyCartesian.ext F.p
    (yoneda.preimage (yoneda.map q))
    (pullArrow F h x (yoneda.preimage (yoneda.map q))) f
  have htrans : (objectSection F h x).map (testRestriction q f) ≫
      pullArrow F h x (yoneda.preimage (yoneda.map q)) =
        pullArrow F h x (yoneda.preimage (yoneda.map (f ≫ q))) := by
    exact pullTransition_fac F h x f (by simp only [CostructuredArrow.mk_hom_eq_self,
      yoneda.preimage_map])
  rw [Category.assoc, htrans, hfac, Category.assoc, hfac, hca]

private theorem conjugate_naturality {C : Type w} [Category.{v} C]
    {X Y X' Y' A B A' B' : C} (α : X ≅ A) (β : Y ≅ B)
    (α' : X' ≅ A') (β' : Y' ≅ B') (γ : A ≅ B) (γ' : A' ≅ B')
    (c : X' ⟶ X) (d : Y' ⟶ Y) (a : A' ⟶ A) (b : B' ⟶ B)
    (hx : α'.hom ≫ a = c ≫ α.hom) (hy : β'.hom ≫ b = d ≫ β.hom)
    (hγ : γ'.hom ≫ b = a ≫ γ.hom) :
    (α' ≪≫ γ' ≪≫ β'.symm).hom ≫ d = c ≫ (α ≪≫ γ ≪≫ β.symm).hom := by
  apply (cancel_mono β.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    ((α'.hom ≫ γ'.hom ≫ β'.inv) ≫ d) ≫ β.hom =
        α'.hom ≫ γ'.hom ≫ β'.inv ≫ (β'.hom ≫ b) := by rw [hy]; simp [Category.assoc]
    _ = α'.hom ≫ (γ'.hom ≫ b) := by simp
    _ = (α'.hom ≫ a) ≫ γ.hom := by rw [hγ]; simp [Category.assoc]
    _ = c ≫ α.hom ≫ γ.hom := by rw [hx]; simp [Category.assoc]
    _ = (c ≫ α.hom ≫ γ.hom ≫ β.inv) ≫ β.hom := by simp [Category.assoc]

/-- For two objects of a DM stack over `T`, the Isom functor is represented by an
algebraic space over `T`, unramified on every representable etale scheme chart.
Source: Stacks Project, Tags 06N3 (3) implies (1), 06MB(1), 045G, 04SI and 03ZJ
(blueprint: lem-sfb-dm-isom-space-unramified).

Here `a` and `b` are lifts of `q`, hence cartesian because the category is fibred
in groupoids. The family `e` identifies points over `q` with isomorphisms between
these pullbacks. Its final equation is precisely restriction of isomorphisms:
`alpha'` is the restriction of `alpha` exactly when `alpha' ≫ d = c ≫ alpha`.

Proof:
1. Take the surjective etale scheme atlas from
   def-sfb-stable-pointed-moduli-groupoids. Each scheme chart of each base change
   is smooth by lem-weil-pbc-etale-smooth-zero-dimensional-fibres. This is a smooth
   surjective scheme atlas, so the stack is algebraic in the required convention.
2. Apply lem-sfb-unramified-diagonal-etale-atlas to obtain its unramified relative
   diagonal from this etale atlas (Stacks 06N3 and 06MB(1)).
3. Base change the diagonal by `(x,y)`. Its algebraic-space representative `I`
   represents Isom: a triple `(z,alpha,beta)` maps to `alpha.inv ≫ beta`; conversely
   `gamma` gives `(q*x,1,gamma)`. Two triples with the same gamma have a unique
   compatible arrow. These constructions commute with pullback (Stacks 04SI, 045G),
   yielding the bijections `e` and their displayed naturality for all lifts.
4. For any representable etale chart of `I`, apply the every-base-change/every-chart
   clause of the unramified diagonal to this base change. Its composite to `T`
   is unramified, meaning locally finite type with open-immersion diagonal
   (def-weil-unramified-morphism; base-change stability is Stacks 03ZJ). -/
theorem dm_isom_space_unramified {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsDeligneMumfordModuliStack F)
    (T : Over S) (x y : Functor.Fiber F.p T) :
    ∃ (I : AlgebraicSpace S) (p : I.obj.obj ⟶ yoneda.obj T),
      (∀ (V : Over S) (b : yoneda.obj V ⟶ I.obj.obj), AlgebraicSpace.IsEtale b →
        IsUnramified ((yoneda.preimage (b ≫ p)).left)) ∧
      ∃ e : ∀ (U : Over S) (q : U ⟶ T) (xU yU : Functor.Fiber F.p U)
          (a : xU.val ⟶ x.val) (b : yU.val ⟶ y.val),
          F.p.IsHomLift q a → F.p.IsHomLift q b →
          {z : I.obj.obj.obj (op U) // p.app (op U) z = q} ≃ (xU ≅ yU),
        ∀ (U U' : Over S) (f : U' ⟶ U) (q : U ⟶ T)
          (xU yU : Functor.Fiber F.p U) (xU' yU' : Functor.Fiber F.p U')
          (a : xU.val ⟶ x.val) (b : yU.val ⟶ y.val)
          (a' : xU'.val ⟶ x.val) (b' : yU'.val ⟶ y.val)
          (ha : F.p.IsHomLift q a) (hb : F.p.IsHomLift q b)
          (ha' : F.p.IsHomLift (f ≫ q) a') (hb' : F.p.IsHomLift (f ≫ q) b')
          (c : xU'.val ⟶ xU.val) (d : yU'.val ⟶ yU.val),
          F.p.IsHomLift f c → F.p.IsHomLift f d → c ≫ a = a' → d ≫ b = b' →
          ∀ (z : {z : I.obj.obj.obj (op U) // p.app (op U) z = q})
            (z' : {z : I.obj.obj.obj (op U') // p.app (op U') z = f ≫ q}),
            z'.val = I.obj.obj.map f.op z.val →
            (e U' (f ≫ q) xU' yU' a' b' ha' hb' z').hom.val ≫ d =
              c ≫ (e U q xU yU a b ha hb z).hom.val := by
  classical
  have hsmooth : ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      ∀ (V : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj V)) F),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj V),
          HasSpaceBaseChange a V t Z p ∧ SpaceMapIsSurjective Z V p ∧
          ∀ (W : Over S) (b : yoneda.obj W ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
            Smooth ((yoneda.preimage (b ≫ p)).left) := by
    obtain ⟨U, a, ha⟩ := hF.2.2
    refine ⟨U, a, fun V t ↦ ?_⟩
    obtain ⟨Z, p, hbc, he, hsurj⟩ := ha V t
    refine ⟨Z, p, hbc, hsurj, fun W b hb ↦ ?_⟩
    have := he W b hb
    infer_instance
  have hdiag := (unramifiedModuliDiagonal_iff_etaleAtlas F hF.1 hF.2.1 hsmooth).2.mpr hF
  let a := objectSection F hF.1.1 x
  let b := objectSection F hF.1.1 y
  obtain ⟨Z, p, hp, E, hE, ⟨E₁⟩, ⟨E₂⟩⟩ := hdiag T T a b
  let n := normalizedComparison F a b Z p E E₁ E₂
  have hn := normalizedComparison_vertical F a b Z p E E₁ E₂
  have hN : (normalizedFunctor F a b Z p n hn).IsEquivalence := by
    have := hE
    exact Functor.isEquivalence_of_iso (normalizedFunctorIso F a b Z p E E₁ E₂)
  let W := AlgebraicSpace.schemeSpace T
  let H := AlgebraicSpace.schemeSpace (Limits.prod T T)
  let P : Z ⟶ H := ObjectProperty.homMk ⟨p⟩
  let D : W ⟶ H := ObjectProperty.homMk ⟨yoneda.map (Limits.prod.lift (𝟙 T) (𝟙 T))⟩
  let I := AlgebraicSpace.enlargedFibreProduct P D
  let j : I.obj.obj ⟶ Z.obj.obj := (Limits.pullback.fst P.hom D.hom).hom
  let pI : I.obj.obj ⟶ yoneda.obj T := (Limits.pullback.snd P.hom D.hom).hom
  have sq : IsPullback j pI p (yoneda.map (Limits.prod.lift (𝟙 T) (𝟙 T))) :=
    (sheafToPresheaf _ _).map_isPullback (IsPullback.of_hasPullback P.hom D.hom)
  refine ⟨I, pI, space_unramified_pullback Z I p pI j _ sq hp, ?_⟩
  let e (U : Over S) (q : U ⟶ T) (xU yU : Functor.Fiber F.p U)
      (c : xU.val ⟶ x.val) (d : yU.val ⟶ y.val)
      (hc : F.p.IsHomLift q c) (hd : F.p.IsHomLift q d) :=
    (diagonalSectionEquiv Z I T p pI j sq U q).trans
      ((fiberSectionEquiv F a b Z p n hn hN q q).trans
        (Iso.isoCongr (arbitraryComparison F hF.1.1 x q xU c hc).symm
          (arbitraryComparison F hF.1.1 y q yU d hd).symm))
  refine ⟨e, ?_⟩
  intro U U' f q xU yU xU' yU' c d c' d' hc hd hc' hd' k l hk hl hkc hld z z' hz
  let z₀ := diagonalSectionEquiv Z I T p pI j sq U q z
  let z₁ := diagonalSectionEquiv Z I T p pI j sq U' (f ≫ q) z'
  have hres : yoneda.map f ≫ z₀.val = z₁.val := by
    change yoneda.map f ≫ yonedaEquiv.symm (j.app (op U) z.val) =
      yonedaEquiv.symm (j.app (op U') z'.val)
    rw [yonedaEquiv_symm_naturality_left]
    apply congrArg yonedaEquiv.symm
    rw [hz]
    exact (ConcreteCategory.congr_hom (j.naturality f.op) z.val).symm
  have hrestriction := sectionComparison_naturality F a b Z p n hn q q f
    z₀.val z₁.val z₀.property z₁.property hres
  have hx := arbitraryComparison_naturality F hF.1.1 x q f xU xU' c c' hc hc' k hk hkc
  have hy := arbitraryComparison_naturality F hF.1.1 y q f yU yU' d d' hd hd' l hl hld
  let C := (Functor.Fiber.fiberInclusion : Functor.Fiber F.p U ⥤ F.obj)
  let C' := (Functor.Fiber.fiberInclusion : Functor.Fiber F.p U' ⥤ F.obj)
  have hnat := conjugate_naturality
    (C.mapIso (arbitraryComparison F hF.1.1 x q xU c hc))
    (C.mapIso (arbitraryComparison F hF.1.1 y q yU d hd))
    (C'.mapIso (arbitraryComparison F hF.1.1 x (f ≫ q) xU' c' hc'))
    (C'.mapIso (arbitraryComparison F hF.1.1 y (f ≫ q) yU' d' hd'))
    (sectionComparison F a b Z p n hn q q z₀.val z₀.property)
    (sectionComparison F a b Z p n hn (f ≫ q) (f ≫ q) z₁.val z₁.property)
    k l (a.map (testRestriction q f)) (b.map (testRestriction q f)) hx hy hrestriction
  exact hnat

end CategoryTheory
