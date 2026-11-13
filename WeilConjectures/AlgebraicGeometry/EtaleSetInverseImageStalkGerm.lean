/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Stalks of inverse images of étale sheaves of sets, with germs

Source: Stacks Project, Étale Cohomology, Tag 03Q1 (3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Tag 03Q1 (3).
The unique map from the inverse-image stalk to the image-point stalk sends every germ of
a unit-pulled-back section to its original germ and is bijective. The pointed neighbourhood
on the source is the fibre product, with lift given by `pullback.lift`. -/
theorem etaleSetInverseImageStalkGerm (S T : Scheme.{u}) (e : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃ c : (Scheme.pointSmallEtale t).sheafFiber.obj ((Scheme.etaleSetPullback e).obj G) →
        (Scheme.pointSmallEtale (t ≫ e)).sheafFiber.obj G,
      Function.Bijective c ∧
      (∀ (U : S.Etale) (x : (Scheme.pointSmallEtale (t ≫ e)).fiber.obj U)
          (a : G.obj.obj (op U)),
        c ((Scheme.pointSmallEtale t).toPresheafFiber
          ((MorphismProperty.Over.pullback @Etale ⊤ e).obj U)
          (Over.homMk (pullback.lift x.left t (Over.w x))
            (pullback.lift_snd x.left t (Over.w x)))
          ((Scheme.etaleSetPullback e).obj G).obj
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U) a)) =
          (Scheme.pointSmallEtale (t ≫ e)).toPresheafFiber U x G.obj a) ∧
      ∀ d : (Scheme.pointSmallEtale t).sheafFiber.obj ((Scheme.etaleSetPullback e).obj G) →
          (Scheme.pointSmallEtale (t ≫ e)).sheafFiber.obj G,
        (∀ (U : S.Etale) (x : (Scheme.pointSmallEtale (t ≫ e)).fiber.obj U)
            (a : G.obj.obj (op U)),
          d ((Scheme.pointSmallEtale t).toPresheafFiber
            ((MorphismProperty.Over.pullback @Etale ⊤ e).obj U)
            (Over.homMk (pullback.lift x.left t (Over.w x))
              (pullback.lift_snd x.left t (Over.w x)))
            ((Scheme.etaleSetPullback e).obj G).obj
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
              (S.smallGrothendieckTopology @Etale)
              (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U) a)) =
            (Scheme.pointSmallEtale (t ≫ e)).toPresheafFiber U x G.obj a) → d = c := by
  let i : Scheme.etaleSetPullback e ⋙ (Scheme.pointSmallEtale t).sheafFiber ≅
      (Scheme.pointSmallEtale (t ≫ e)).sheafFiber :=
    Functor.isoWhiskerRight
        (Functor.sheafPullbackConstruction.sheafPullbackIso
          (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1)) _ _).symm _ ≪≫
      (GrothendieckTopology.Point.sheafFiberComapIso (Scheme.pointSmallEtale t) e.Etale
        (Scheme.Hom.coverPreserving_etale e) (Type (u + 1))).symm ≪≫
      GrothendieckTopology.Point.sheafFiberIso (Scheme.pointSmallEtaleComapIso e t)
  have hformula : ∀ (U : S.Etale)
      (x : (Scheme.pointSmallEtale (t ≫ e)).fiber.obj U),
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
          (S.smallGrothendieckTopology @Etale)
          (T.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op U)) ≫
        (Scheme.pointSmallEtale t).toPresheafFiber (e.Etale.obj U)
          ((Scheme.pointSmallEtaleFiberEtaleIso e t).inv.app U x)
          ((Scheme.etaleSetPullback e).obj G).obj ≫ (i.app G).hom =
        (Scheme.pointSmallEtale (t ≫ e)).toPresheafFiber U x G.obj := by
    intro U x
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv _).1
    simp only [i, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Category.assoc]
    rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
    rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
    rw [show (Scheme.pointSmallEtale t).sheafFiber.map _ =
      (Scheme.pointSmallEtale t).presheafFiber.map _ from rfl,
      GrothendieckTopology.Point.toPresheafFiber_naturality]
    have hu := Adjunction.unit_leftAdjointUniq_hom_app
      (Functor.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
        (S.smallGrothendieckTopology (P := @Etale))
        (T.smallGrothendieckTopology (P := @Etale)))
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
        (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)) G
    have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
    rw [← Category.assoc, ← huU]
    rfl
  have hx : ∀ (U : S.Etale) (x : (Scheme.pointSmallEtale (t ≫ e)).fiber.obj U),
      (Scheme.pointSmallEtaleFiberEtaleIso e t).inv.app U x =
        Over.homMk (pullback.lift x.left t (Over.w x))
          (pullback.lift_snd x.left t (Over.w x)) := by
    intro U x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change _ = pullback.lift x.left t (Over.w x) ≫ pullback.fst U.hom e
      erw [pullback.lift_fst]
      exact Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst e t U x
    · change _ = pullback.lift x.left t (Over.w x) ≫ pullback.snd U.hom e
      erw [pullback.lift_snd]
      exact Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd e t U x
  refine ⟨(i.app G).hom, ?_, ?_, ?_⟩
  · exact (ConcreteCategory.bijective_of_isIso (i.app G).hom)
  · intro U x a
    have h := ConcreteCategory.congr_hom (hformula U x) a
    rw [hx] at h
    simp only [types_comp_apply] at h
    exact h
  · intro d hd
    funext z
    obtain ⟨U, x, a, ha⟩ :=
      (Scheme.pointSmallEtale (t ≫ e)).toPresheafFiber_jointly_surjective
        (P := G.obj) ((i.app G).hom z)
    have hf := ConcreteCategory.congr_hom (hformula U x) a
    rw [hx] at hf
    simp only [types_comp_apply, Scheme.Hom.Etale] at hf
    have hz := (ConcreteCategory.bijective_of_isIso (i.app G).hom).1 (hf.trans ha)
    rw [← hz]
    exact (hd U x a).trans hf.symm

end AlgebraicGeometry
