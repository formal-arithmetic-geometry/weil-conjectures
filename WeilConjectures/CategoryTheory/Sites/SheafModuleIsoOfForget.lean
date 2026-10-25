/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Isomorphisms of sheaves of modules from isomorphisms of underlying abelian sheaves

An isomorphism of the underlying abelian sheaves of two sheaves of `T`-modules which is
`T`-linear on sections is an isomorphism of sheaves of `T`-modules
(`CategoryTheory.Sheaf.isoOfForget₂Iso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C} {T : Type (u + 1)}
  [Ring T]

/-- The sectionwise `T`-linear equivalence underlying `Sheaf.isoOfForget₂Iso`. -/
noncomputable def linearEquivOfForget₂Iso {F G : Sheaf J (ModuleCat.{u + 1} T)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj G)
    (he : ∀ (U : Cᵒᵖ) (t : T) (x : F.obj.obj U),
      e.hom.hom.app U (t • x) =
        @HSMul.hSMul T (G.obj.obj U) (G.obj.obj U) _ t (e.hom.hom.app U x)) (U : Cᵒᵖ) :
    F.obj.obj U ≃ₗ[T] G.obj.obj U where
  toFun x := e.hom.hom.app U x
  invFun y := e.inv.hom.app U y
  left_inv x := Iso.hom_inv_id_apply (((sheafToPresheaf J _).mapIso e).app U) x
  right_inv y := Iso.inv_hom_id_apply (((sheafToPresheaf J _).mapIso e).app U) y
  map_add' := map_add (e.hom.hom.app U).hom
  map_smul' := he U

/-- An isomorphism `e` of the underlying abelian sheaves of two sheaves of `T`-modules which is
`T`-linear on sections is an isomorphism of sheaves of `T`-modules. -/
noncomputable def isoOfForget₂Iso {F G : Sheaf J (ModuleCat.{u + 1} T)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj G)
    (he : ∀ (U : Cᵒᵖ) (t : T) (x : F.obj.obj U),
      e.hom.hom.app U (t • x) =
        @HSMul.hSMul T (G.obj.obj U) (G.obj.obj U) _ t (e.hom.hom.app U x)) :
    F ≅ G :=
  (fullyFaithfulSheafToPresheaf J _).preimageIso
    (NatIso.ofComponents (fun U ↦ (linearEquivOfForget₂Iso e he U).toModuleIso) fun {U V} φ ↦ by
      ext x
      exact ConcreteCategory.congr_hom (e.hom.hom.naturality φ) x)

/-- The underlying map of `Sheaf.isoOfForget₂Iso e he` on sections is that of `e`. -/
@[simp]
lemma isoOfForget₂Iso_hom_hom_app_apply {F G : Sheaf J (ModuleCat.{u + 1} T)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{u + 1} T) Ab.{u + 1})).obj G)
    (he : ∀ (U : Cᵒᵖ) (t : T) (x : F.obj.obj U),
      e.hom.hom.app U (t • x) =
        @HSMul.hSMul T (G.obj.obj U) (G.obj.obj U) _ t (e.hom.hom.app U x))
    (U : Cᵒᵖ) (x : F.obj.obj U) :
    (isoOfForget₂Iso e he).hom.hom.app U x = e.hom.hom.app U x :=
  rfl

end CategoryTheory.Sheaf
