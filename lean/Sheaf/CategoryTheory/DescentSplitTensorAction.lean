/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Descent of a ring action and a split retraction

Source: Stacks Project, Categories, Tags 04VI, 04VJ and 04VK.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uD vD uE vE r

open CategoryTheory

namespace CategoryTheory

/-- Precomposition by a full essentially surjective functor is fully faithful.
Source: Stacks Project, Categories, Tag 04VI
(blueprint: lem-pur-descent-split-tensor-action).
Proof: conjugate each component by a chosen image isomorphism. Fullness lifts a
morphism between chosen preimages and proves naturality. The original naturality
square at each image isomorphism proves the two inverse identities. -/
theorem bijective_whiskerLeft_of_full_essSurj
    {A : Type uA} [Category.{vA} A] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] (L : A ⥤ D) [L.Full] [L.EssSurj]
    (U V : D ⥤ E) : Function.Bijective
      (fun τ : U ⟶ V ↦ Functor.whiskerLeft L τ) := by
  classical
  have extn {α β : U ⟶ V} (h : Functor.whiskerLeft L α = Functor.whiskerLeft L β) :
      α = β := by
    ext X
    apply (cancel_epi (U.map (L.objObjPreimageIso X).hom)).1
    rw [α.naturality, β.naturality]
    exact congrArg (fun t ↦ t.app (L.objPreimage X) ≫
      V.map (L.objObjPreimageIso X).hom) h
  refine ⟨fun _ _ h ↦ extn h, ?_⟩
  intro α
  let β : U ⟶ V :=
    { app := fun X ↦ U.map (L.objObjPreimageIso X).inv ≫
        α.app (L.objPreimage X) ≫ V.map (L.objObjPreimageIso X).hom
      naturality := by
        intro X Y f
        let g := L.preimage ((L.objObjPreimageIso X).hom ≫ f ≫
          (L.objObjPreimageIso Y).inv)
        have h := α.naturality g
        change U.map (L.map g) ≫ α.app (L.objPreimage Y) =
          α.app (L.objPreimage X) ≫ V.map (L.map g) at h
        dsimp only [g] at h
        rw [L.map_preimage] at h
        have h' := congrArg (fun t ↦ U.map (L.objObjPreimageIso X).inv ≫ t ≫
          V.map (L.objObjPreimageIso Y).hom) h
        simpa only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
          Iso.map_hom_inv_id, Iso.map_inv_hom_id, Category.comp_id] using h' }
  refine ⟨β, ?_⟩
  ext X
  let g := L.preimage (L.objObjPreimageIso (L.obj X)).hom
  have h := α.naturality g
  change U.map (L.map g) ≫ α.app X =
    α.app (L.objPreimage (L.obj X)) ≫ V.map (L.map g) at h
  dsimp only [g] at h
  rw [L.map_preimage] at h
  change U.map (L.objObjPreimageIso (L.obj X)).inv ≫
    α.app (L.objPreimage (L.obj X)) ≫ V.map (L.objObjPreimageIso (L.obj X)).hom = _
  rw [← h]
  simp

/-- Fully faithful precomposition is invariant under a natural isomorphism.
Source: Stacks Project, Categories, Tag 04VI
(blueprint: lem-pur-descent-split-tensor-action).
Proof: conjugate a transformation by the image of the given isomorphism, lift it
along the original precomposition functor, and use naturality to cancel the
isomorphism. -/
theorem bijective_whiskerLeft_of_iso
    {A : Type uA} [Category.{vA} A] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] {L M : A ⥤ D} (i : L ≅ M)
    (U V : D ⥤ E)
    (h : Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft L τ)) :
    Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft M τ) := by
  constructor
  · intro α β hab
    apply h.1
    ext X
    apply (cancel_mono (V.map (i.hom.app X))).1
    change α.app _ ≫ V.map (i.hom.app X) = β.app _ ≫ V.map (i.hom.app X)
    rw [← α.naturality, ← β.naturality]
    exact congrArg (fun t ↦ U.map (i.hom.app X) ≫ t.app X) hab
  · intro α
    let β : L ⋙ U ⟶ L ⋙ V :=
      Functor.whiskerRight i.hom U ≫ α ≫ Functor.whiskerRight i.inv V
    obtain ⟨γ, hγ⟩ := h.2 β
    refine ⟨γ, ?_⟩
    ext X
    have hh := congrArg (fun t ↦ t.app X) hγ
    dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at hh
    apply (cancel_epi (U.map (i.hom.app X))).1
    change U.map (i.hom.app X) ≫ γ.app _ = _
    rw [γ.naturality, hh]
    simp only [Category.assoc, ← V.map_comp, i.inv_hom_id_app, V.map_id]
    exact congrArg (fun t ↦ U.map (i.hom.app X) ≫ t) (Category.comp_id (α.app X))

/-- Fully faithful precomposition descends an action and a split retraction together.
Source: Stacks Project, Categories, Tags 04VI, 04VJ and 04VK
(blueprint: lem-pur-descent-split-tensor-action).
Proof: lift each transformation by fullness. Faithfulness proves the ring-homomorphism
laws and the two composite identities after precomposition. The resulting equalities
also record the normalization of every lifted transformation. -/
theorem exists_splitAction_of_bijective_whiskerLeft
    {A : Type uA} [Category.{vA} A] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] [Preadditive E]
    (L : A ⥤ D)
    (h : ∀ U V : D ⥤ E, Function.Bijective
      (fun τ : U ⟶ V ↦ Functor.whiskerLeft L τ))
    {R : Type r} [Ring R] (e : R) (U V : D ⥤ E)
    (a : R →+* End (L ⋙ U)) (b : L ⋙ U ⟶ L ⋙ V) (s : L ⋙ V ⟶ L ⋙ U)
    (hsb : s ≫ b = 𝟙 _) (hbs : b ≫ s = a e) :
    ∃ (a' : R →+* End U) (b' : U ⟶ V) (s' : V ⟶ U),
      s' ≫ b' = 𝟙 V ∧ b' ≫ s' = a' e ∧
      (∀ x, Functor.whiskerLeft L (a' x) = a x) ∧
      Functor.whiskerLeft L b' = b ∧ Functor.whiskerLeft L s' = s := by
  classical
  let lift {X Y : D ⥤ E} (t : L ⋙ X ⟶ L ⋙ Y) : X ⟶ Y := (h X Y).2 t |>.choose
  have hlift {X Y : D ⥤ E} (t : L ⋙ X ⟶ L ⋙ Y) :
      Functor.whiskerLeft L (lift t) = t := (h X Y).2 t |>.choose_spec
  let a' : R →+* End U :=
    { toFun := fun x ↦ lift (a x)
      map_zero' := by
        apply (h U U).1
        change Functor.whiskerLeft L (lift (a 0)) = 0
        simpa using hlift (a 0)
      map_one' := by
        apply (h U U).1
        change Functor.whiskerLeft L (lift (a 1)) = 𝟙 _
        simpa using hlift (a 1)
      map_add' := by
        intro x y
        apply (h U U).1
        change Functor.whiskerLeft L (lift (a (x + y))) = _
        rw [hlift]
        change a (x + y) = Functor.whiskerLeft L (lift (a x)) +
          Functor.whiskerLeft L (lift (a y))
        rw [hlift, hlift, map_add]
      map_mul' := by
        intro x y
        apply (h U U).1
        change Functor.whiskerLeft L (lift (a (x * y))) = _
        rw [hlift]
        change a (x * y) = Functor.whiskerLeft L (lift (a y)) ≫
          Functor.whiskerLeft L (lift (a x))
        rw [hlift, hlift]
        exact a.map_mul x y }
  refine ⟨a', lift b, lift s, ?_, ?_, fun x ↦ hlift (a x), hlift b, hlift s⟩
  · apply (h V V).1
    simpa only [Functor.whiskerLeft_comp, hlift, Functor.whiskerLeft_id'] using hsb
  · apply (h U U).1
    change Functor.whiskerLeft L (lift b ≫ lift s) =
      Functor.whiskerLeft L (lift (a e))
    simpa only [Functor.whiskerLeft_comp, hlift] using hbs

private noncomputable def mapEndRing {X Y : Type*} [Category X] [Category Y]
    [Preadditive X] [Preadditive Y] (G : X ⥤ Y) [G.Additive] (x : X) :
    End x →+* End (G.obj x) :=
  { G.mapEnd x with map_zero' := G.map_zero _ _, map_add' := fun _ _ ↦ G.map_add }

private noncomputable def conjugateEndRing {X : Type*} [Category X] [Preadditive X]
    {x y : X} (i : x ≅ y) : End x →+* End y where
  toFun t := i.inv ≫ t ≫ i.hom
  map_zero' := by simp
  map_one' := by simp only [End.one_def, Category.id_comp, Iso.inv_hom_id]
  map_add' _ _ := by
    change i.inv ≫ (_ + _) ≫ i.hom = _
    simp only [Preadditive.comp_add, Preadditive.add_comp]
  map_mul' _ _ := by simp only [End.mul_def, Category.assoc, Iso.hom_inv_id_assoc]

/-- Transport a split action across comparison isomorphisms and descend it.
Source: Stacks Project, Categories, Tags 04VI--04VK
(blueprint: lem-pur-descent-split-tensor-action).
Proof: conjugate the mapped action and the mapped retraction by the comparisons.
The isomorphism identities preserve the ring laws and the two splitting identities.
Apply fully faithful precomposition descent and cancel each comparison to obtain
its normalization square. -/
theorem exists_splitAction_of_comparison
    {A : Type uA} [Category.{vA} A] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E] [Preadditive E]
    {X : Type*} [Category X] [Preadditive X]
    (L : A ⥤ D)
    (h : ∀ U V : D ⥤ E, Function.Bijective
      (fun τ : U ⟶ V ↦ Functor.whiskerLeft L τ))
    (G : X ⥤ (A ⥤ E)) [G.Additive] {x y : X}
    (U V : D ⥤ E) (α : G.obj x ≅ L ⋙ U) (β : G.obj y ≅ L ⋙ V)
    {R : Type r} [Ring R] (e : R) (a : R →+* End x) (b : x ⟶ y) (s : y ⟶ x)
    (hsb : s ≫ b = 𝟙 _) (hbs : b ≫ s = a e) :
    ∃ (a' : R →+* End U) (b' : U ⟶ V) (s' : V ⟶ U),
      s' ≫ b' = 𝟙 V ∧ b' ≫ s' = a' e ∧
      (∀ t, G.map (a t) ≫ α.hom = α.hom ≫ Functor.whiskerLeft L (a' t)) ∧
      G.map b ≫ β.hom = α.hom ≫ Functor.whiskerLeft L b' := by
  let aa : R →+* End (L ⋙ U) :=
    (conjugateEndRing α).comp ((mapEndRing G x).comp a)
  let bb := α.inv ≫ G.map b ≫ β.hom
  let ss := β.inv ≫ G.map s ≫ α.hom
  have hss : ss ≫ bb = 𝟙 _ := by
    dsimp only [ss, bb]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp_assoc,
      hsb, G.map_id, Category.id_comp, Iso.inv_hom_id]
  have hbb : bb ≫ ss = aa e := by
    dsimp only [ss, bb]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp_assoc, hbs]
    rfl
  obtain ⟨a', b', s', hs, hp, ha, hb, _⟩ :=
    exists_splitAction_of_bijective_whiskerLeft L h e U V aa bb ss hss hbb
  refine ⟨a', b', s', hs, hp, ?_, ?_⟩
  · intro t
    rw [ha]
    change G.map (a t) ≫ α.hom = α.hom ≫ α.inv ≫ G.map (a t) ≫ α.hom
    exact (α.hom_inv_id_assoc _).symm
  · rw [hb]
    exact (α.hom_inv_id_assoc _).symm

end CategoryTheory
