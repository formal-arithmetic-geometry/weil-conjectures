/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Karoubi extension of systems, morphisms and compatible transformations

The extension is defined by the supported projector formulas of Mathlib.
Source: sketch32, lines 1208--1228 and 1313--1321.
(blueprint: lem-sbc-stage-system-karoubi-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Idempotents

namespace CategoryTheory.StageSystem
variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]

/-- Systems are equal when their transition and associator data agree. -/
theorem system_ext {S T : StageSystem C} (hT : @S.T = @T.T)
    (ha : HEq (@S.assoc) (@T.assoc)) : S = T := by
  cases S
  cases T
  cases hT
  cases ha
  rfl

/-- Extend a scalar system by the supported Karoubi formulas. -/
def karSystem (S : StageSystem C) : StageSystem (fun i ↦ Karoubi (C i)) where
  T h := (functorExtension₂ _ _).obj (S.T h)
  assoc h k := (functorExtension₂ _ _).mapIso (S.assoc h k)
  cocycle {i j k m} h h' h'' P := by
    have he :
        Functor.whiskerRight ((functorExtension₂ _ _).map (S.assoc h h').hom)
            ((functorExtension₂ _ _).obj (S.T h'')) ≫
          (functorExtension₂ _ _).map (S.assoc (h.trans h') h'').hom =
        Functor.whiskerLeft ((functorExtension₂ _ _).obj (S.T h))
            ((functorExtension₂ _ _).map (S.assoc h' h'').hom) ≫
          (functorExtension₂ _ _).map (S.assoc h (h'.trans h'')).hom := by
      apply (whiskeringLeftObjToKaroubiFullyFaithful (C := C i) (D := Karoubi (C m))).map_injective
      ext K
      simp only [Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
        NatTrans.comp_app, Functor.whiskerRight_app]
      simpa [Functor.map_comp, functorExtension₂, functorExtension₁,
        FunctorExtension₁.obj, FunctorExtension₁.map] using S.cocycle h h' h'' K
    exact congrArg (fun α ↦ α.app P) he
end CategoryTheory.StageSystem

namespace CategoryTheory.StageSystem
universe u' v'
variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {T : StageSystem D}

/-- Extend a coherent family of functors to every projector. -/
def karMorphism (F : Morphism S T) : Morphism (karSystem S) (karSystem T) where
  Φ i := (functorExtension₂ _ _).obj (F.Φ i)
  β h := (functorExtension₂ _ _).mapIso (F.β h)
  coh {i j k} h h' P := by
    have he :
        Functor.whiskerRight ((functorExtension₂ _ _).map (F.β h).hom)
            ((functorExtension₂ _ _).obj (T.T h')) ≫
          Functor.whiskerLeft ((functorExtension₂ _ _).obj (S.T h))
            ((functorExtension₂ _ _).map (F.β h').hom) ≫
          Functor.whiskerRight ((functorExtension₂ _ _).map (S.assoc h h').hom)
            ((functorExtension₂ _ _).obj (F.Φ k)) =
        Functor.whiskerLeft ((functorExtension₂ _ _).obj (F.Φ i))
            ((functorExtension₂ _ _).map (T.assoc h h').hom) ≫
          (functorExtension₂ _ _).map (F.β (h.trans h')).hom := by
      apply (whiskeringLeftObjToKaroubiFullyFaithful
        (C := C i) (D := Karoubi (D k))).map_injective
      ext K
      simpa [Functor.map_comp, functorExtension₂, functorExtension₁,
        FunctorExtension₁.obj, FunctorExtension₁.map] using F.coh h h' K
    exact congrArg (fun α ↦ α.app P) he

/-- Extend a compatible transformation to every projector. -/
def karHom {F G : Morphism S T} (α : Morphism.Hom F G) :
    Morphism.Hom (karMorphism F) (karMorphism G) where
  τ i := (functorExtension₂ _ _).map (α.τ i)
  comm {i j} h P := by
    have he :
        Functor.whiskerRight ((functorExtension₂ _ _).map (α.τ i))
            ((functorExtension₂ _ _).obj (T.T h)) ≫
          (functorExtension₂ _ _).map (G.β h).hom =
        (functorExtension₂ _ _).map (F.β h).hom ≫
          Functor.whiskerLeft ((functorExtension₂ _ _).obj (S.T h))
            ((functorExtension₂ _ _).map (α.τ j)) := by
      apply (whiskeringLeftObjToKaroubiFullyFaithful
        (C := C i) (D := Karoubi (D j))).map_injective
      ext K
      simpa [Functor.map_comp, functorExtension₂, functorExtension₁,
        FunctorExtension₁.obj, FunctorExtension₁.map] using α.comm h K
    exact congrArg (fun η ↦ η.app P) he
/-- Change the endpoint systems along equalities. -/
def castMorphism {S' : StageSystem C} {T' : StageSystem D}
    (hS : S = S') (hT : T = T') (F : Morphism S T) : Morphism S' T' := by
  subst S'; subst T'
  exact F

theorem castMorphism_obj {S' : StageSystem C} {T' : StageSystem D}
    (hS : S = S') (hT : T = T') (F : Morphism S T) (i : I) :
    (castMorphism hS hT F).Φ i = F.Φ i := by
  subst S'; subst T'; rfl

theorem castMorphism_beta {S' : StageSystem C} {T' : StageSystem D}
    (hS : S = S') (hT : T = T') (F : Morphism S T) {i j : I} (h : i ≤ j) :
    HEq ((castMorphism hS hT F).β h) (F.β h) := by
  subst S'; subst T'; rfl

/-- Change the endpoint systems of a compatible transformation. -/
def castHom {S' : StageSystem C} {T' : StageSystem D}
    (hS : S = S') (hT : T = T') {F G : Morphism S T} (α : Morphism.Hom F G) :
    Morphism.Hom (castMorphism hS hT F) (castMorphism hS hT G) := by
  subst S'; subst T'
  exact α

theorem castHom_tau {S' : StageSystem C} {T' : StageSystem D}
    (hS : S = S') (hT : T = T') {F G : Morphism S T}
    (α : Morphism.Hom F G) (i : I) :
    HEq ((castHom hS hT α).τ i) (α.τ i) := by
  subst S'; subst T'; rfl

end CategoryTheory.StageSystem

namespace CategoryTheory.Idempotents
universe a b x y
variable {A : Type a} [Category.{x} A] {B : Type b} [Category.{y} B]

/-- Additivity of the supported extension follows on underlying arrows. -/
instance extension_additive [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] : ((functorExtension₂ _ _).obj F).Additive where
  map_add := by
    intros
    apply Karoubi.hom_ext
    exact F.map_add

/-- Mapping transformations respects transport of equal endpoint functors. -/
theorem extension_map_heq {F G F' G' : A ⥤ B}
    (hF : F = F') (hG : G = G') (α : F ⟶ G) (β : F' ⟶ G')
    (h : HEq α β) :
    HEq ((functorExtension₂ _ _).map α) ((functorExtension₂ _ _).map β) := by
  subst F'; subst G'
  cases h
  rfl

/-- A normalized raw comparison remains normalized after supported extension. -/
theorem mapIso_unit {U : A ⥤ A} {V : B ⥤ B}
    (F : A ⥤ B) (b : F ⋙ V ≅ U ⋙ F)
    (hU : U = 𝟭 A) (hV : V = 𝟭 B) (hb : HEq b (Iso.refl F)) :
    HEq ((functorExtension₂ _ _).mapIso b)
      (Iso.refl ((functorExtension₂ _ _).obj F)) := by
  subst U; subst V
  have hb' : b = Iso.refl F := eq_of_heq hb
  subst b
  exact heq_of_eq ((functorExtension₂ _ _).mapIso_refl F)

end CategoryTheory.Idempotents

namespace CategoryTheory.StageSystem
universe u' v'
variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {T : StageSystem D}
  {S' : StageSystem (fun i ↦ Karoubi (C i))}
  {T' : StageSystem (fun i ↦ Karoubi (D i))}
  (hS : karSystem S = S') (hT : karSystem T = T')

theorem castKarMorphism_obj (F : Morphism S T) (i : I) :
    (castMorphism hS hT (karMorphism F)).Φ i =
      (functorExtension₂ _ _).obj (F.Φ i) :=
  castMorphism_obj hS hT (karMorphism F) i

theorem castKarMorphism_beta (F : Morphism S T) {i j : I} (h : i ≤ j) :
    HEq ((castMorphism hS hT (karMorphism F)).β h)
      ((functorExtension₂ _ _).mapIso (F.β h)) :=
  castMorphism_beta hS hT (karMorphism F) h

theorem castKarMorphism_unit (F : Morphism S T)
    (uS : ∀ i, S.T (le_refl i) = 𝟭 (C i))
    (uT : ∀ i, T.T (le_refl i) = 𝟭 (D i))
    (uF : ∀ i, HEq (F.β (le_refl i)) (Iso.refl (F.Φ i))) (i : I) :
    HEq ((castMorphism hS hT (karMorphism F)).β (le_refl i))
      (Iso.refl ((castMorphism hS hT (karMorphism F)).Φ i)) := by
  subst S'; subst T'
  exact mapIso_unit (F.Φ i) (F.β (le_refl i)) (uS i) (uT i) (uF i)

theorem castKarHom_tau {F G : Morphism S T} (α : Morphism.Hom F G) (i : I) :
    HEq ((castHom hS hT (karHom α)).τ i)
      ((functorExtension₂ _ _).map (α.τ i)) :=
  castHom_tau hS hT (karHom α) i

end CategoryTheory.StageSystem

namespace CategoryTheory.StageSystem
universe u' v'
variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {T : StageSystem D}
  {S' : StageSystem (fun i ↦ Karoubi (C i))}
  {T' : StageSystem (fun i ↦ Karoubi (D i))}

/-- A supported morphism has exactly the extended objects and comparisons and strict units. -/
def KarMorphismSpec (F : Morphism S T) (K : Morphism S' T') : Prop :=
  (∀ i, K.Φ i = (functorExtension₂ _ _).obj (F.Φ i)) ∧
  (∀ {i j} (h : i ≤ j), HEq (K.β h) ((functorExtension₂ _ _).mapIso (F.β h))) ∧
  ∀ i, HEq (K.β (le_refl i)) (Iso.refl (K.Φ i))

/-- Transport the supported morphism, retaining the full component API. -/
theorem karMorphism_exists (hS : karSystem S = S') (hT : karSystem T = T')
    (F : Morphism S T)
    (uS : ∀ i, S.T (le_refl i) = 𝟭 (C i))
    (uT : ∀ i, T.T (le_refl i) = 𝟭 (D i))
    (uF : ∀ i, HEq (F.β (le_refl i)) (Iso.refl (F.Φ i))) :
    ∃ K : Morphism S' T', KarMorphismSpec F K := by
  refine ⟨castMorphism hS hT (karMorphism F), castKarMorphism_obj hS hT F,
    castKarMorphism_beta hS hT F, castKarMorphism_unit hS hT F uS uT uF⟩

/-- Transport a compatible transformation and both supported morphisms together. -/
theorem karHom_exists (hS : karSystem S = S') (hT : karSystem T = T')
    {F G : Morphism S T} (α : Morphism.Hom F G)
    (uS : ∀ i, S.T (le_refl i) = 𝟭 (C i))
    (uT : ∀ i, T.T (le_refl i) = 𝟭 (D i))
    (uF : ∀ i, HEq (F.β (le_refl i)) (Iso.refl (F.Φ i)))
    (uG : ∀ i, HEq (G.β (le_refl i)) (Iso.refl (G.Φ i))) :
    ∃ (K L : Morphism S' T'), ∃ η : Morphism.Hom K L,
      KarMorphismSpec F K ∧ KarMorphismSpec G L ∧
      ∀ i, HEq (η.τ i) ((functorExtension₂ _ _).map (α.τ i)) := by
  refine ⟨castMorphism hS hT (karMorphism F), castMorphism hS hT (karMorphism G),
    castHom hS hT (karHom α), ?_, ?_, castKarHom_tau hS hT α⟩
  · exact ⟨castKarMorphism_obj hS hT F, castKarMorphism_beta hS hT F,
      castKarMorphism_unit hS hT F uS uT uF⟩
  · exact ⟨castKarMorphism_obj hS hT G, castKarMorphism_beta hS hT G,
      castKarMorphism_unit hS hT G uS uT uG⟩

end CategoryTheory.StageSystem
