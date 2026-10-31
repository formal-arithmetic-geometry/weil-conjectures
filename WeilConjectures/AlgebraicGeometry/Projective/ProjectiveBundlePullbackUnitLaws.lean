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

/-- The identity pullback comparison agrees with the two composite unit comparisons.
Source: Stacks Project, Sheaves, Tag 0097; Constructions Tag 01O3
(blueprint: lem-pur-projective-bundle-pullback-unit-laws). -/
theorem projectiveBundlePullback_unit_square
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    (he : (𝟙 X) ≫ f = f ≫ (𝟙 Y)) :
    (projectiveBundlePullbackId X).hom.app ((Scheme.Modules.tensorPullback f).obj F) =
      ((projectiveBundlePullbackComp (𝟙 X) f).app F).hom ≫
        (projectiveBundlePullbackCongr he).hom.app F ≫
        ((projectiveBundlePullbackComp f (𝟙 Y)).app F).inv ≫
        (Scheme.Modules.tensorPullback f).map ((projectiveBundlePullbackId Y).hom.app F) := by
  let er := (projectiveBundlePullbackComp (𝟙 X) f).app F
  let el := (projectiveBundlePullbackComp f (𝟙 Y)).app F
  have hr := congrArg (fun k ↦ k.app F) (projectiveBundlePullback_right_unitality f)
  have hl := congrArg (fun k ↦ k.app F) (projectiveBundlePullback_left_unitality f)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app] at hr hl
  have hr' : er.inv ≫
      (projectiveBundlePullbackId X).hom.app ((Scheme.Modules.tensorPullback f).obj F) =
      eqToHom (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj F)
        (Category.id_comp f)) := by
    exact (congrArg (er.inv ≫ ·) (Category.comp_id _)).symm.trans
      (hr.trans (eqToHom_app _ _))
  have hl' : el.inv ≫
      (Scheme.Modules.tensorPullback f).map ((projectiveBundlePullbackId Y).hom.app F) =
      eqToHom (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj F)
        (Category.comp_id f)) := by
    exact (congrArg (el.inv ≫ ·) (Category.comp_id _)).symm.trans
      (hl.trans (eqToHom_app _ _))
  calc
    _ = er.hom ≫ eqToHom (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj F)
        (Category.id_comp f)) := by
      apply (cancel_epi er.inv).mp
      simpa only [Category.assoc, er.inv_hom_id_assoc] using hr'
    _ = er.hom ≫ (projectiveBundlePullbackCongr he).hom.app F ≫
        eqToHom (congrArg (fun g ↦ (Scheme.Modules.tensorPullback g).obj F)
          (Category.comp_id f)) := by
      simp [projectiveBundlePullbackCongr]
    _ = _ := by rw [← hl']

/-- The identity line comparison preserves a normalized projective-bundle quotient.
Source: Stacks Project, Sheaves, Tag 0097; Constructions Tag 01O3
(blueprint: lem-pur-projective-bundle-pullback-unit-laws). -/
theorem projectiveBundleThetaQuotientLaw_identity
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (r : D.A.data.relProj ⟶ D.A.data.relProj) (hr : r = 𝟙 _)
    (ho : r ≫ D.A.data.relProjHom = D.A.data.relProjHom ≫ (𝟙 B)) :
    projectiveBundleThetaQuotientLaw D D (𝟙 B)
      ((projectiveBundlePullbackId B).app F).symm r ho
      ((projectiveBundlePullbackCongr hr).app D.L ≪≫
        (projectiveBundlePullbackId D.A.data.relProj).app D.L) := by
  subst r
  change (Scheme.Modules.tensorPullback (𝟙 D.A.data.relProj)).map D.quotient ≫
      (projectiveBundlePullbackId D.A.data.relProj).hom.app D.L = _
  calc
    _ = (projectiveBundlePullbackId D.A.data.relProj).hom.app
        ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F) ≫ D.quotient :=
      (projectiveBundlePullbackId D.A.data.relProj).hom.naturality D.quotient
    _ = _ := congrArg (fun t ↦ t ≫ D.quotient)
      (projectiveBundlePullback_unit_square D.A.data.relProjHom F ho)

end AlgebraicGeometry
