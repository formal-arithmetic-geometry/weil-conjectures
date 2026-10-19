/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionData
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom

/-! # Normalization of the étale projection comparison

Source: Stacks Project, Tag 0GKF.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped DirectSum TensorProduct

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma etaleLiftSection_iso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale) :
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
      (inferInstance : Etale e)).inv.app N).hom.app (op W) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app N).hom.app
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) ≫
        ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj.map
          (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
            (inferInstance : Etale e) trivial).unit.app W).op) := by
  let i := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
    (inferInstance : Etale e)
  let j := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
    (inferInstance : Etale e) trivial
  apply (cancel_mono ((i.hom.app N).hom.app (op W))).mp
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e)
    (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) e
      (inferInstance : Etale e)) N
  have huW := congr_app (Sheaf.hom_ext_iff.1 hu)
    (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
  rw [Category.assoc]
  erw [(i.hom.app N).hom.naturality (j.unit.app W).op]
  change _ =
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app N).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) ≫
      (i.hom.app N).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ e).obj
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))) ≫ _
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at huW
  erw [huW]
  erw [localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  change _ = N.obj.map (j.counit.app _).op ≫
    N.obj.map ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).map
      (j.unit.app W)).op
  rw [← N.obj.map_comp]
  rw [← op_comp]
  erw [j.left_triangle_components W]
  change _ = N.obj.map (𝟙 (op ((MorphismProperty.Over.map ⊤
    (inferInstance : Etale e)).obj W)))
  rw [N.obj.map_id]
  exact congr_app (Sheaf.hom_ext_iff.1 (i.inv_hom_id_app N)) (op W)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_ulift_germ (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W) :
    (Scheme.pointSmallEtale t).ulift.{u + 1}.toPresheafFiber W (ULift.up w) P ≫
      ((Scheme.pointSmallEtale t).uliftPresheafFiberIso (ModuleCat.{u + 1} A)).hom.app P =
    (Scheme.pointSmallEtale t).toPresheafFiber W w P := by
  exact Functor.Final.ι_colimitIso_hom
    (Functor.Elements.uliftEquivalence.{u + 1} (Scheme.pointSmallEtale t).fiber).functor.op
    ((CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙ P)
    (op ⟨W, ULift.up w⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_tensor_germ (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X)
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W) :
    let := (sheafificationAdjunction X.smallEtaleTopology
      (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
    ((Scheme.pointSmallEtale t).toPresheafFiber W w M.obj ⊗ₘ
      (Scheme.pointSmallEtale t).toPresheafFiber W w N.obj) ≫
        (etaleProjectionTensorStalkIso A t M N).inv =
      (Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) M N).app (op W) ≫
          (Scheme.pointSmallEtale t).toPresheafFiber W w
            (etaleSheafTensor A X M N).obj := by
  let := (sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
  simp only [etaleProjectionTensorStalkIso, Iso.trans_inv, tensorIso_inv,
    Iso.symm_inv, Iso.app_inv, sheafFiberTensorIso_inv]
  have hM := projection_ulift_germ A t M.obj W w
  have hN := projection_ulift_germ A t N.obj W w
  have hMN := projection_ulift_germ A t (etaleSheafTensor A X M N).obj W w
  have hMi := (Iso.comp_inv_eq _).2 hM.symm
  have hNi := (Iso.comp_inv_eq _).2 hN.symm
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  erw [hMi, hNi]
  rw [Category.assoc]
  erw [reassoc_of% (Scheme.etale_stalk_tensor_unique t M N).2.1 W (ULift.up w)]
  erw [hMN]

-- The proof of the canonical unit-germ equation of Tag 03Q1 is coefficient-independent.
private theorem etaleProjection_inverseImage_stalk_germ
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (U : X.Etale)
        (ū : (Scheme.pointSmallEtale (y ≫ f)).fiber.obj U),
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app G).hom.app
              (op U) ≫
            (Scheme.pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
              ((Scheme.pointSmallEtaleFiberEtaleIso f y).inv.app U ū)
              ((Etale.upperStar (ModuleCat.{u + 1} A) f).obj G).obj ≫
            ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f y).app G).hom =
          (Scheme.pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  intro G U ū
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv _).1
  simp only [Etale.upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (Scheme.pointSmallEtale y).sheafFiber.map _ =
    (Scheme.pointSmallEtale y).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (ModuleCat.{u + 1} A)
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_lift_germ (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ V)
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale)
    (w : (Scheme.pointSmallEtale s).fiber.obj W)
    (n : N.obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))) :
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) e s).app N).hom
        ((Scheme.pointSmallEtale s).toPresheafFiber W w
          ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj
            (etaleLiftSection A e N W n)) =
      (Scheme.pointSmallEtale (s ≫ e)).toPresheafFiber
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
        (Over.homMk w.left (by
          change w.left ≫ (W.hom ≫ e) = s ≫ e
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun k ↦ k ≫ e) (Over.w w)))) N.obj n := by
  let Z := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W
  let z : (Scheme.pointSmallEtale (s ≫ e)).fiber.obj Z :=
    Over.homMk w.left (by
      change w.left ≫ (W.hom ≫ e) = s ≫ e
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ e) (Over.w w)))
  let a := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
    (inferInstance : Etale e) trivial).unit.app W
  have hw : (Scheme.pointSmallEtale s).fiber.map a w =
      (Scheme.pointSmallEtaleFiberEtaleIso e s).inv.app Z z := by
    apply ((Scheme.pointSmallEtaleFiberEtaleIso e s).app Z).toEquiv.injective
    change (Scheme.pointSmallEtaleFiberEtaleIso e s).hom.app Z
      ((Scheme.pointSmallEtale s).fiber.map a w) =
      (Scheme.pointSmallEtaleFiberEtaleIso e s).hom.app Z
        ((Scheme.pointSmallEtaleFiberEtaleIso e s).inv.app Z z)
    erw [Iso.inv_hom_id_app_apply]
    apply Over.OverMorphism.ext
    change (w.left ≫ pullback.lift (𝟙 W.left) W.hom _) ≫
      pullback.fst (W.hom ≫ e) e = w.left
    simp
  have hg := (Scheme.pointSmallEtale s).toPresheafFiber_w a w
    ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj
  rw [hw] at hg
  have h := etaleProjection_inverseImage_stalk_germ A e s N Z z
  have h' := congrArg (fun k ↦ k n) h
  simp only [ModuleCat.comp_apply] at h'
  dsimp only [etaleLiftSection]
  have hg' := congrArg (fun k ↦ k
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app N).hom.app
      (op Z) n)) hg
  simp only [ModuleCat.comp_apply] at hg'
  exact (congrArg
    (((upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) e s).app N).hom) hg').trans h'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_tensor_hom_ext (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    {Q : ModuleCat.{u + 1} A}
    {f g : ((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} A)).obj M ⊗
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)).obj N ⟶ Q}
    (h : ∀ (W : X.Etale) (w : (Scheme.pointSmallEtale s).fiber.obj W)
      (m : M.obj.obj (op W)) (n : N.obj.obj (op W)),
      f ((Scheme.pointSmallEtale s).toPresheafFiber W w M.obj m ⊗ₜ[A]
        (Scheme.pointSmallEtale s).toPresheafFiber W w N.obj n) =
      g ((Scheme.pointSmallEtale s).toPresheafFiber W w M.obj m ⊗ₜ[A]
        (Scheme.pointSmallEtale s).toPresheafFiber W w N.obj n)) : f = g := by
  apply (cancel_epi (Functor.OplaxMonoidal.δ
    (Scheme.pointSmallEtale s).presheafFiber M.obj N.obj)).mp
  apply (Scheme.pointSmallEtale s).presheafFiber_hom_ext
  intro W w
  rw [GrothendieckTopology.Point.toPresheafFiber_δ_assoc,
    GrothendieckTopology.Point.toPresheafFiber_δ_assoc]
  apply ModuleCat.hom_ext
  refine TensorProduct.ext (LinearMap.ext fun m ↦ LinearMap.ext fun n ↦ ?_)
  exact h W w m n

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_sum_germ (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (v : Over.mk t ⟶ Over.mk e) (W : V.Etale)
    (w : (Scheme.pointSmallEtale v.left).fiber.obj W) (m : M.obj.obj (op W)) :
    (etaleProjectionSumStalkIso A e t M).hom
        ((Scheme.pointSmallEtale t).toPresheafFiber
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
          (Over.homMk w.left (by
            change w.left ≫ (W.hom ≫ e) = t
            have hw : w.left ≫ W.hom = v.left := Over.w w
            rw [← Category.assoc, hw]
            exact Over.w v))
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj
          (etaleSumSection A e M W m)) =
      DirectSum.lof A _
        (fun z : Over.mk t ⟶ Over.mk e ↦
          ((Scheme.pointSmallEtale z.left).sheafFiber
            (A := ModuleCat.{u + 1} A)).obj M) v
        ((Scheme.pointSmallEtale v.left).toPresheafFiber W w M.obj m) := by
  obtain ⟨s, hs, rfl⟩ := Over.homMk_surjective v
  obtain ⟨a, ha, rfl⟩ := Over.homMk_surjective w
  change (Spec (.of Ω) ⟶ V) at s
  change (Spec (.of Ω) ⟶ W.left) at a
  change a ≫ W.hom = s at ha
  subst s
  exact (exists_etaleSumStalksIso e A Ω t).choose_spec.2 M W
    (Over.homMk a (by
      change a ≫ (W.hom ≫ e) = t
      exact (Category.assoc _ _ _).symm.trans hs)) m

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_lift_germ_over (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (v : Over.mk t ⟶ Over.mk e)
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale)
    (w : (Scheme.pointSmallEtale v.left).fiber.obj W)
    (z : (Scheme.pointSmallEtale t).fiber.obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
    (hz : z.left = w.left)
    (n : N.obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))) :
    (etaleProjectionLiftStalkIso A e t v N).hom
        ((Scheme.pointSmallEtale v.left).toPresheafFiber W w
          ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj
            (etaleLiftSection A e N W n)) =
      (Scheme.pointSmallEtale t).toPresheafFiber
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z N.obj n := by
  obtain ⟨s, hs, rfl⟩ := Over.homMk_surjective v
  change (Spec (.of Ω) ⟶ V) at s
  change s ≫ e = t at hs
  subst t
  have h := projection_lift_germ A e s N W w n
  let z' : (Scheme.pointSmallEtale (s ≫ e)).fiber.obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) :=
    Over.homMk w.left (by
      change w.left ≫ (W.hom ≫ e) = s ≫ e
      have hw : w.left ≫ W.hom = s := Over.w w
      rw [← Category.assoc, hw])
  have hz' : z = z' := by
    apply Over.OverMorphism.ext
    exact hz
  rw [hz']
  exact h

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_source_germ (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (v : Over.mk t ⟶ Over.mk e) (W : V.Etale)
    (w : (Scheme.pointSmallEtale v.left).fiber.obj W)
    (z : (Scheme.pointSmallEtale t).fiber.obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
    (hz : z.left = w.left) (m : M.obj.obj (op W))
    (n : N.obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))) :
    (etaleProjectionSourceStalkIso A e t M N).inv
        (DirectSum.lof A _
          (fun v : Over.mk t ⟶ Over.mk e ↦
            ((Scheme.pointSmallEtale v.left).sheafFiber
              (A := ModuleCat.{u + 1} A)).obj M) v
          ((Scheme.pointSmallEtale v.left).toPresheafFiber W w M.obj m) ⊗ₜ[A]
            (Scheme.pointSmallEtale t).toPresheafFiber
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
              z N.obj n) =
      (Scheme.pointSmallEtale t).toPresheafFiber
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z
        (etaleSheafTensor A T
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) N).obj
        (etaleSheafTensorSection A _ N
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
          (etaleSumSection A e M W m) n) := by
  let z' : (Scheme.pointSmallEtale t).fiber.obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) :=
    Over.homMk w.left (by
      change w.left ≫ (W.hom ≫ e) = t
      have hw : w.left ≫ W.hom = v.left := Over.w w
      rw [← Category.assoc, hw]
      exact Over.w v)
  have h := projection_sum_germ A e t M v W w m
  have hz' : z = z' := by
    apply Over.OverMorphism.ext
    exact hz
  change (etaleProjectionSumStalkIso A e t M).hom
    ((Scheme.pointSmallEtale t).toPresheafFiber
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z'
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj
      (etaleSumSection A e M W m)) = _ at h
  rw [← hz'] at h
  change (etaleProjectionTensorStalkIso A t _ N).inv
    (((etaleProjectionSumStalkIso A e t M).inv
      (DirectSum.lof A _ _ v
        ((Scheme.pointSmallEtale v.left).toPresheafFiber W w M.obj m))) ⊗ₜ[A]
          (Scheme.pointSmallEtale t).toPresheafFiber
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z N.obj n) = _
  rw [← h]
  have hi := congrArg (fun k ↦ k
    ((Scheme.pointSmallEtale t).toPresheafFiber
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj
      (etaleSumSection A e M W m))) (etaleProjectionSumStalkIso A e t M).hom_inv_id
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hi
  rw [hi]
  exact congrArg (fun k ↦ k (etaleSumSection A e M W m ⊗ₜ[A] n))
    (projection_tensor_germ A t _ N
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z)

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_target_germ (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (v : Over.mk t ⟶ Over.mk e) (W : V.Etale)
    (w : (Scheme.pointSmallEtale v.left).fiber.obj W)
    (z : (Scheme.pointSmallEtale t).fiber.obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
    (hz : z.left = w.left) (m : M.obj.obj (op W))
    (n : N.obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))) :
    (etaleProjectionTargetStalkIso A e t M N).hom
      ((Scheme.pointSmallEtale t).toPresheafFiber
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj
          (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N))).obj
        (etaleSumSection A e _ W
          (etaleSheafTensorSection A M _ W m (etaleLiftSection A e N W n)))) =
      DirectSum.lof A _
        (fun v : Over.mk t ⟶ Over.mk e ↦ TensorProduct A
          (((Scheme.pointSmallEtale v.left).sheafFiber
            (A := ModuleCat.{u + 1} A)).obj M)
          (((Scheme.pointSmallEtale t).sheafFiber
            (A := ModuleCat.{u + 1} A)).obj N)) v
        ((Scheme.pointSmallEtale v.left).toPresheafFiber W w M.obj m ⊗ₜ[A]
          (Scheme.pointSmallEtale t).toPresheafFiber
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z N.obj n) := by
  let z' : (Scheme.pointSmallEtale t).fiber.obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) :=
    Over.homMk w.left (by
      change w.left ≫ (W.hom ≫ e) = t
      have hw : w.left ≫ W.hom = v.left := Over.w w
      rw [← Category.assoc, hw]
      exact Over.w v)
  have hz' : z = z' := by
    apply Over.OverMorphism.ext
    exact hz
  have hs := projection_sum_germ A e t
    (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N))
    v W w (etaleSheafTensorSection A M _ W m (etaleLiftSection A e N W n))
  change (etaleProjectionSumStalkIso A e t
      (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N))).hom
    ((Scheme.pointSmallEtale t).toPresheafFiber
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z'
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj
        (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N))).obj
      (etaleSumSection A e _ W
        (etaleSheafTensorSection A M _ W m (etaleLiftSection A e N W n)))) = _ at hs
  rw [← hz'] at hs
  dsimp only [etaleProjectionTargetStalkIso, Iso.trans_hom]
  rw [CategoryTheory.comp_apply, hs]
  change DirectSum.congrLinearEquiv _ (DirectSum.lof A _ _ v _) = _
  rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  congr 1
  change (tensorIso (Iso.refl _) (etaleProjectionLiftStalkIso A e t v N)).hom
    ((etaleProjectionTensorStalkIso A v.left M _).hom
      ((Scheme.pointSmallEtale v.left).toPresheafFiber W w
        (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N)).obj
        (etaleSheafTensorSection A M _ W m (etaleLiftSection A e N W n)))) = _
  have ht := congrArg (fun k ↦ k (m ⊗ₜ[A] etaleLiftSection A e N W n))
    (projection_tensor_germ A v.left M ((upperStar (ModuleCat.{u + 1} A) e).obj N) W w)
  have ht' := congrArg (etaleProjectionTensorStalkIso A v.left M _).hom ht
  change (etaleProjectionTensorStalkIso A v.left M _).hom
    ((etaleProjectionTensorStalkIso A v.left M _).inv
      ((Scheme.pointSmallEtale v.left).toPresheafFiber W w M.obj m ⊗ₜ[A]
        (Scheme.pointSmallEtale v.left).toPresheafFiber W w
          ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj
          (etaleLiftSection A e N W n))) = _ at ht'
  rw [ModuleCat.hom_inv_apply] at ht'
  simp only [CategoryTheory.comp_apply] at ht'
  erw [← ht']
  simp only [tensorIso_hom, Iso.refl_hom,
    ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.id_apply]
  erw [projection_lift_germ_over A e t v N W w z hz n]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A sheaf morphism satisfying the summand-section formula has the normalized
geometric-stalk square. This is independent of any proof that the morphism is invertible
or natural in its sheaf arguments.

Source: Stacks Project, Tag 0GKF, geometric-stalk square; Tags 03S5 and 03Q1
(blueprint: lem-pur-etale-projection-stalk-normalization).

Proof: cancel the source stalk comparison and the direct-sum tensor comparison.
Direct-sum induction reduces to one lift summand. Precompose with the tensor of the
identity and the inverse-image stalk comparison, which is an isomorphism. The
oplax tensorator of the filtered stalk colimit and its colimit universal property
reduce to pure tensors of two section germs on the same source neighbourhood.
The localization comparison for an étale map expresses every inverse-image section
as the graph-restricted unit of a target section on the composed neighbourhood.
The germ formula of exists_etaleSumStalksIso
identifies the sum generator with the germ of etaleSumSection. The tensor-stalk unit
formula identifies their pure tensor with the germ of etaleSheafTensorSection.
Naturality of germs and the assumed section formula compute its image. Apply the
target sum-stalk formula and tensor-stalk formula. The inverse-image stalk comparison
sends the germ of the graph-restricted unit to the original target germ, by the
unit-germ equation and compatibility with pointed restriction. Each generator is
therefore sent to its same lift summand containing the pure tensor of the two germs.
This is precisely TensorProduct.directSumLeft. Additivity and the colimit universal
property conclude. The empty fibre gives zero source and target and causes no exception. -/
theorem etaleProjection_stalk_normalization (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (p : etaleSheafTensor A T
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) N ⟶
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj
        (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N)))
    (hp : ∀ (W : V.Etale) (m : M.obj.obj (op W))
      (n : N.obj.obj
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))),
      p.hom.app (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
          (etaleSheafTensorSection A _ N
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
            (etaleSumSection A e M W m) n) =
        etaleSumSection A e _ W
          (etaleSheafTensorSection A M _ W m (etaleLiftSection A e N W n)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).map p ≫
        (etaleProjectionTargetStalkIso A e t M N).hom =
      (etaleProjectionSourceStalkIso A e t M N).hom ≫
        (etaleProjectionDirectSumTensorIso A e t M N).hom := by
  classical
  apply (cancel_epi ((etaleProjectionSourceStalkIso A e t M N).inv)).mp
  rw [Iso.inv_hom_id_assoc]
  apply (cancel_epi ((etaleProjectionDirectSumTensorIso A e t M N).inv)).mp
  rw [Iso.inv_hom_id]
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro v
  let i := ModuleCat.ofHom (DirectSum.lof A (Over.mk t ⟶ Over.mk e)
    (fun z ↦ TensorProduct A
      (((Scheme.pointSmallEtale z.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj M)
      (((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)).obj N)) v)
  suffices h : i ≫ (etaleProjectionDirectSumTensorIso A e t M N).inv ≫
      (etaleProjectionSourceStalkIso A e t M N).inv ≫
        (Scheme.pointSmallEtale t).sheafFiber.map p ≫
          (etaleProjectionTargetStalkIso A e t M N).hom = i by
    exact congrArg ModuleCat.Hom.hom h
  apply (cancel_epi (tensorIso (Iso.refl _)
    (etaleProjectionLiftStalkIso A e t v N)).hom).mp
  apply projection_tensor_hom_ext A v.left M
    ((upperStar (ModuleCat.{u + 1} A) e).obj N)
  intro W w m n'
  let j := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
    (inferInstance : Etale e)
  let n := ((j.hom.app N).hom.app (op W)) n'
  have hn : etaleLiftSection A e N W n = n' := by
    change (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app N).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) ≫
        ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj.map
          (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
            (inferInstance : Etale e) trivial).unit.app W).op)) n = n'
    rw [← etaleLiftSection_iso]
    exact ModuleCat.inv_hom_apply
      ((sheafToPresheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
        (j.app N) |>.app (op W)) n'
  rw [← hn]
  let z : (Scheme.pointSmallEtale t).fiber.obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) :=
    Over.homMk w.left (by
      change w.left ≫ (W.hom ≫ e) = t
      have hw : w.left ≫ W.hom = v.left := Over.w w
      rw [← Category.assoc, hw]
      exact Over.w v)
  have hl := projection_lift_germ_over A e t v N W w z rfl n
  simp only [CategoryTheory.comp_apply, tensorIso_hom,
    ModuleCat.MonoidalCategory.tensorHom_tmul, Iso.refl_hom, ModuleCat.id_apply]
  rw [hl]
  have hd (x : ((Scheme.pointSmallEtale v.left).sheafFiber
      (A := ModuleCat.{u + 1} A)).obj M)
      (y : ((Scheme.pointSmallEtale t).sheafFiber
        (A := ModuleCat.{u + 1} A)).obj N) :
      (etaleProjectionDirectSumTensorIso A e t M N).inv (i (x ⊗ₜ[A] y)) =
        DirectSum.lof A (Over.mk t ⟶ Over.mk e)
          (fun z ↦ ((Scheme.pointSmallEtale z.left).sheafFiber
            (A := ModuleCat.{u + 1} A)).obj M) v x ⊗ₜ[A] y := by
    exact TensorProduct.directSumLeft_symm_lof_tmul A A
      (M₁ := fun z : Over.mk t ⟶ Over.mk e ↦
        ((Scheme.pointSmallEtale z.left).sheafFiber
          (A := ModuleCat.{u + 1} A)).obj M)
      (M₂' := ((Scheme.pointSmallEtale t).sheafFiber
        (A := ModuleCat.{u + 1} A)).obj N) v x y
  erw [hd ((Scheme.pointSmallEtale v.left).toPresheafFiber W w M.obj m)
    ((Scheme.pointSmallEtale t).toPresheafFiber
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z N.obj n)]
  erw [projection_source_germ A e t M N v W w z rfl m n]
  have hg := (Scheme.pointSmallEtale t).toPresheafFiber_naturality p.hom
    ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) z
  have hg' := congrArg (fun k ↦ k
    (etaleSheafTensorSection A _ N
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
      (etaleSumSection A e M W m) n)) hg
  simp only [CategoryTheory.comp_apply] at hg'
  erw [hg', hp]
  exact projection_target_germ A e t M N v W w z rfl m n

end AlgebraicGeometry.Etale
