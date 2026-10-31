/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarCompositeModelPasting
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization

/-! # Scalar extension and composition of open extensions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
attribute [local implicit_reducible] CommMon.toMon scalarSixPull

private instance openCompositionRing_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X :=
  Λ.comm

private instance openCompositionMap_isMonHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

private instance openCompositionCoefficient_isMonHom {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    IsMonHom (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X) := by
  change IsMonHom ((upperStarFromPoint X).map a.hom.hom)
  infer_instance

private theorem scalarComposition
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {La : A ⥤ D} {Ra : D ⥤ A} {Lb : B ⥤ E} {Rb : E ⥤ B}
    {Lc : C ⥤ F} {Rc : F ⥤ C}
    {H : A ⥤ B} {S : B ⥤ A} {I : B ⥤ C} {T : C ⥤ B}
    {J : A ⥤ C} {U : C ⥤ A}
    {P : D ⥤ E} {Rp : E ⥤ D} {Q : E ⥤ F} {Rq : F ⥤ E}
    {R : D ⥤ F} {Rr : F ⥤ D}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc)
    (h : H ⊣ S) (i : I ⊣ T) (j : J ⊣ U)
    (p : P ⊣ Rp) (q : Q ⊣ Rq) (r : R ⊣ Rr)
    (α01 : Rp ⋙ Ra ≅ Rb ⋙ S) (α12 : Rq ⋙ Rb ≅ Rc ⋙ T)
    (α02 : Rr ⋙ Ra ≅ Rc ⋙ U) (β : U ≅ T ⋙ S) (γ : Rq ⋙ Rp ≅ Rr)
    (μ : J ≅ H ⋙ I) (κ : R ≅ P ⋙ Q)
    (hμ : conjugateIsoEquiv (h.comp i) j μ = β.symm)
    (hκ : conjugateIsoEquiv (p.comp q) r κ = γ)
    (hr : α02 = Functor.isoWhiskerRight γ.symm Ra ≪≫
      Functor.associator Rq Rp Ra ≪≫ Functor.isoWhiskerLeft Rq α01 ≪≫
      (Functor.associator Rq Rb S).symm ≪≫ Functor.isoWhiskerRight α12 S ≪≫
      Functor.associator Rc T S ≪≫ Functor.isoWhiskerLeft Rc β.symm)
    (K : A) :
    Lc.map (μ.inv.app K) ≫
        ((conjugateIsoEquiv (a.comp r) (j.comp c)).symm α02).hom.app K =
      ((conjugateIsoEquiv (b.comp q) (i.comp c)).symm α12).hom.app (H.obj K) ≫
        Q.map (((conjugateIsoEquiv (a.comp p) (h.comp b)).symm α01).hom.app K) ≫
          κ.inv.app (La.obj K) := by
  let t01 := (conjugateIsoEquiv (a.comp p) (h.comp b)).symm α01
  let t12 := (conjugateIsoEquiv (b.comp q) (i.comp c)).symm α12
  let t02 := (conjugateIsoEquiv (a.comp r) (j.comp c)).symm α02
  have he := adjunctionSquareComposition a b c h i j p q r
    α01 α12 α02 β γ t01.symm t12.symm t02.symm μ κ.symm
    (by simp only [t01, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply])
    (by simp only [t12, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply])
    (by simp only [t02, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]) hμ
    (by rw [conjugateIsoEquiv_iso_symm, hκ]) hr
  have he' := congrArg (fun z ↦ z.inv.app K) he
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id] at he'
  have hh := congrArg (fun z ↦ z ≫ κ.inv.app (La.obj K)) he'.symm
  simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc, Category.comp_id] using hh

set_option maxHeartbeats 2000000 in
-- Compare the derived adjunction presentations without expanding their resolutions.
/-- Scalar extension commutes with the canonical compositor for two open extensions.
Source: latest blueprint, scalar-six compact-support proof,
Independence and Composition.
(blueprint: lem-sfb-scalar-open-composition).

Proof: the inverse open comparison has mate the normalized scalar pullback comparison.
Apply horizontal
mate pasting and the conjugate characterization of the two open compositors. The pullback
composition equation identifies the two mates, hence the two inverse open comparisons. Evaluate
at the object and cancel the invertible factors to obtain the forward equation. -/
theorem scalarOpenComposition {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a Z).map ((sfbScalarOpenComp Λ f g).hom.app M) ≫
      (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
        a.hom.hom a.hom.isMonHom_hom _ _ (f ≫ g) _).hom.app M =
    (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
        a.hom.hom a.hom.isMonHom_hom _ _ g _).hom.app
        ((openImmersionLowerShriek Λ.X f).mapDerivedCategory.obj M) ≫
      (openImmersionLowerShriek Λ'.X g).mapDerivedCategory.map
        ((@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
          a.hom.hom a.hom.isMonHom_hom _ _ f _).hom.app M) ≫
      (sfbScalarOpenComp Λ' f g).hom.app ((scalarSixChange a X).obj M) := by
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  let sx := scalarSixScalarAdjunction a X
  let sb := scalarSixScalarAdjunction a Y
  let sc := scalarSixScalarAdjunction a Z
  let hj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X f
  let hi := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X g
  let hc := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (f ≫ g)
  let pj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X f
  let pi := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X g
  let pc := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X (f ≫ g)
  let w := Adjunction.leftAdjointCompIso hj hi hc (scalarSixPullComp Λ f g).symm
  let w' := Adjunction.leftAdjointCompIso pj pi pc (scalarSixPullComp Λ' f g).symm
  have hr : derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom (f ≫ g) =
      Functor.isoWhiskerRight (scalarSixPullComp Λ' f g)
        (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
          a.hom.hom X)).mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (scalarSixPull Λ' g)
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom g)
        (scalarSixPull Λ f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).mapDerivedCategory
        (scalarSixPullComp Λ f g).symm := by
    apply Iso.ext_inv
    apply NatTrans.ext
    funext N
    simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
      Category.comp_id]
    have hh := congrArg (fun z ↦ z ≫
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
        a.hom.hom X)).mapDerivedCategory.map
          ((scalarSixPullComp Λ' f g).inv.app N))
      (scalarSixRestrictionComp a f g N)
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hh
    rw [(Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom X)).mapDerivedCategory.map_id
        ((scalarSixPull Λ' (f ≫ g)).obj N)] at hh
    erw [Category.comp_id] at hh
    simpa only [Category.assoc] using hh
  have h := scalarComposition sx sb sc hj hi hc pj pi pc
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom g)
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom (f ≫ g))
    (scalarSixPullComp Λ f g) (scalarSixPullComp Λ' f g).symm
    w.symm w'.symm
    (by
      dsimp only [w, Adjunction.leftAdjointCompIso]
      exact Equiv.apply_symm_apply _ _)
    (by
      dsimp only [w', Adjunction.leftAdjointCompIso]
      exact Equiv.apply_symm_apply _ _)
    hr M
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
