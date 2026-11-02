/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData

/-! # Coherence of the specified tensor-pullback comparisons
Source: Stacks Project, Sheaves, Tag 0097; Constructions Tag 01O3.
Proof: conjugate the ordinary pullback unit equations by the specified tensor-to-ordinary
isomorphisms, cancel inverse pairs and use naturality. Equality transport commutes with the
comparison family. Combine the two unit equations by cancellation against the composition
isomorphism. Naturality of the identity comparison applied to the quotient gives its square.
(blueprint: lem-pur-projective-bundle-pullback-unit-laws).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Left unit law transported from the ordinary module-pullback pseudofunctor.
Source: Stacks Project, Sheaves, Tag 0097; Constructions Tag 01O3
(blueprint: lem-pur-projective-bundle-pullback-unit-laws). -/
theorem projectiveBundlePullback_left_unitality
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (projectiveBundlePullbackComp f (𝟙 Y)).inv ≫
      Functor.whiskerRight (projectiveBundlePullbackId Y).hom (Scheme.Modules.tensorPullback f) ≫
        (Functor.leftUnitor _).hom = eqToHom (by simp) := by
  unfold projectiveBundlePullbackComp projectiveBundlePullbackId
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_comp, Category.assoc]
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  rw [← (projectiveBundleTensorPullbackIso f).inv.naturality_assoc]
  have h := congrArg (fun k ↦ k.app F) (Scheme.Modules.pseudofunctor_left_unitality f)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  rw [reassoc_of% h]
  have hn := congrArg (fun k ↦ k.app F) (eqToHom_iso_hom_naturality
    (fun g : X ⟶ Y ↦ projectiveBundleTensorPullbackIso g) (Category.comp_id f))
  simp only [NatTrans.comp_app] at hn
  rw [reassoc_of% hn]
  simp

/-- Right unit law transported from the ordinary module-pullback pseudofunctor.
Source: Stacks Project, Sheaves, Tag 0097; Constructions Tag 01O3
(blueprint: lem-pur-projective-bundle-pullback-unit-laws). -/
theorem projectiveBundlePullback_right_unitality
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (projectiveBundlePullbackComp (𝟙 X) f).inv ≫
      Functor.whiskerLeft (Scheme.Modules.tensorPullback f) (projectiveBundlePullbackId X).hom ≫
        (Functor.rightUnitor _).hom = eqToHom (by simp) := by
  unfold projectiveBundlePullbackComp projectiveBundlePullbackId
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_comp, Category.assoc]
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app]
  rw [← (projectiveBundleTensorPullbackIso (𝟙 X)).inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [(Scheme.Modules.pullbackId X).hom.naturality_assoc]
  have h := congrArg (fun k ↦ k.app F) (Scheme.Modules.pseudofunctor_right_unitality f)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  rw [reassoc_of% h]
  have hn := congrArg (fun k ↦ k.app F) (eqToHom_iso_hom_naturality
    (fun g : X ⟶ Y ↦ projectiveBundleTensorPullbackIso g) (Category.id_comp f))
  simp only [NatTrans.comp_app] at hn
  rw [reassoc_of% hn]
  simp

/-- Associativity transported from the ordinary module-pullback pseudofunctor.
Source: Stacks Project, Sheaves, Tag 0097; Constructions Tag 01O3
(blueprint: lem-pur-projective-bundle-pullback-unit-laws). -/
theorem projectiveBundlePullback_associativity
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (projectiveBundlePullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (projectiveBundlePullbackComp g h).inv _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (projectiveBundlePullbackComp f g).hom ≫
        (projectiveBundlePullbackComp (f ≫ g) h).hom = eqToHom (by simp) := by
  unfold projectiveBundlePullbackComp
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  have hn := congrArg (fun t ↦ (Scheme.Modules.tensorPullback f).map t)
    ((projectiveBundleTensorPullbackIso g).hom.naturality
      ((projectiveBundleTensorPullbackIso h).inv.app F))
  simp only [Functor.map_comp] at hn
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (projectiveBundleTensorPullbackIso f).inv.naturality_assoc]
  rw [(projectiveBundleTensorPullbackIso f).hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [(projectiveBundleTensorPullbackIso (f ≫ g)).hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  have hs := (Scheme.Modules.pullbackComp f g).hom.naturality
    ((projectiveBundleTensorPullbackIso h).inv.app F)
  simp only [Functor.comp_map] at hs
  rw [reassoc_of% hs]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  have ha := congrArg (fun k ↦ k.app F)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp] at ha
  rw [reassoc_of% ha]
  have he := congrArg (fun k ↦ k.app F) (eqToHom_iso_hom_naturality
    (fun g : W ⟶ Z ↦ projectiveBundleTensorPullbackIso g) (Category.assoc f g h).symm)
  simp only [NatTrans.comp_app] at he
  rw [reassoc_of% he, Iso.hom_inv_id_app]
  simp

end AlgebraicGeometry
