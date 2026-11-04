/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.AlgebraicGeometry.Curve.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence

/-! # Evaluation and canonical germs of finite etale representatives

Source: coefficient-heart proof (1), pointed finite trivializations.
(blueprint: lem-sfb-coefficient-heart-finite-germs)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology.Point
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The canonical representable-stalk comparison is evaluation at the marked point.
Source: the Yoneda stalk formula, coefficient-heart proof (1).
(blueprint: lem-sfb-coefficient-heart-finite-germs)
Proof: the small representable stalk formula follows from naturality of the shrink-Yoneda
comparison. Whiskering the formula with the universe lift and using the canonical
forgetful stalk comparison gives precisely the published FLC comparison. -/
theorem finiteEtale_germ (v : Spec (.of Ω) ⟶ X) (P : X.FiniteEtale)
    (U : X.Etale) (w : (Scheme.pointSmallEtale v).fiber.obj U) (f : U ⟶ P.obj) :
    (Scheme.FiniteEtale.toFLCCompSheafFiberIso v).hom.app P
      ((Scheme.pointSmallEtale v).toPresheafFiber U w
        ((Scheme.FiniteEtale.toFLC X).obj P).obj.obj (ULift.up f)) =
      ULift.up ((Scheme.pointSmallEtale v).fiber.map f w) := by
  let Φ := Scheme.pointSmallEtale v
  have hs :=
    presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app Φ f w
  have hn := ConcreteCategory.congr_hom
    (Φ.shrinkYonedaCompPresheafFiberIso.hom.naturality f)
    (Φ.shrinkYonedaCompPresheafFiberIso.inv.app U w)
  have small :
      (Functor.isoWhiskerRight X.smallEtaleTopology.yonedaCompSheafToPresheaf
          Φ.presheafFiber ≪≫
        Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm Φ.presheafFiber ≪≫
          Φ.shrinkYonedaCompPresheafFiberIso).hom.app P.obj
        (Φ.toPresheafFiber U w (X.smallEtaleTopology.yoneda.obj P.obj).obj f) =
      Φ.fiber.map f w := by
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, ConcreteCategory.comp_apply]
    erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
      GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
    simp only [Functor.comp_map, ConcreteCategory.comp_apply, Iso.inv_hom_id_app_apply] at hn
    exact (congrArg (ConcreteCategory.hom
      (Φ.shrinkYonedaCompPresheafFiberIso.hom.app P.obj)) hs.symm).trans hn
  let : PreservesFilteredColimitsOfSize.{u, u} uliftFunctor.{u + 1, u} := inferInstance
  have hc := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app uliftFunctor.{u + 1} U w
      (X.smallEtaleTopology.yoneda.obj P.obj).obj)
    (ULift.up f : ULift.{u + 1} (U ⟶ P.obj))
  rw [ConcreteCategory.comp_apply] at hc
  simp only [Scheme.FiniteEtale.toFLCCompSheafFiberIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, ConcreteCategory.comp_apply]
  change uliftFunctor.map _
    (((Φ.presheafFiberCompIso uliftFunctor.{u + 1}).hom.app
      (X.smallEtaleTopology.yoneda.obj P.obj).obj) _) = _
  erw [hc]
  exact congrArg ULift.up small

/-- Bijective evaluation on a finite etale representative is bijective on its set germs.
Source: coefficient-heart proof (1), evaluation on the pointed trivializing cover.
(blueprint: lem-sfb-coefficient-heart-finite-germs)
Proof: the representing sections are the universe lift of morphisms from the cover. The
representable stalk comparison identifies their germs with evaluation at its marked point.
Both universe lifts and the comparison are equivalences, so evaluation detects bijectivity. -/
theorem finiteEtale_germ_bijective (v : Spec (.of Ω) ⟶ X) (P B : X.FiniteEtale)
    (b : (Scheme.FiniteEtale.fiber v).obj B)
    (heval : Function.Bijective
      (fun f : B ⟶ P ↦ (Scheme.FiniteEtale.fiber v).map f b)) :
    Function.Bijective ((Scheme.pointSmallEtale v).toPresheafFiber B.obj b
      ((Scheme.FiniteEtale.toFLC X).obj P).obj.obj) := by
  let e : (B ⟶ P) ≃ ULift.{u + 1} (B.obj ⟶ P.obj) :=
    { toFun := fun f ↦ ULift.up f.hom
      invFun := fun f ↦ ObjectProperty.homMk f.down
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let d := (Scheme.FiniteEtale.toFLCCompSheafFiberIso v).app P
  have ht : Function.Bijective (fun z : ULift.{u + 1} (B.obj ⟶ P.obj) ↦
      ULift.up ((Scheme.FiniteEtale.fiber v).map (e.symm z) b)) :=
    Equiv.ulift.symm.bijective.comp (heval.comp e.symm.bijective)
  have hc : (fun z : ULift.{u + 1} (B.obj ⟶ P.obj) ↦
      d.hom ((Scheme.pointSmallEtale v).toPresheafFiber B.obj b
        ((Scheme.FiniteEtale.toFLC X).obj P).obj.obj z)) =
      (fun z : ULift.{u + 1} (B.obj ⟶ P.obj) ↦
        ULift.up ((Scheme.FiniteEtale.fiber v).map (e.symm z) b)) := by
    funext z
    exact finiteEtale_germ v P B.obj b z.down
  have hh := hc.symm ▸ ht
  exact hh.of_comp_left d.toEquiv.injective

/-- Evaluation bijectivity gives the actual A-linear germ isomorphism.
Source: coefficient-heart proof (1), the unique pointed trivialization.
(blueprint: lem-sfb-coefficient-heart-finite-germs)
Proof: transport the representable set-germ bijection through the representing sheaf
isomorphism. The canonical comparison between set and module stalks identifies this set
germ with the underlying map of the module germ. The module forgetful functor reflects
isomorphisms, so bijectivity gives the stated isomorphism. -/
theorem etaleGerm_isIso_of_representative {A : Type u} [CommRing A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (v : Spec (.of Ω) ⟶ X) (P B : X.FiniteEtale)
    (e : ((Scheme.FiniteEtale.toFLC X).obj P).obj ≅ (etaleSet A X).obj F)
    (b : (Scheme.FiniteEtale.fiber v).obj B)
    (heval : Function.Bijective
      (fun f : B ⟶ P ↦ (Scheme.FiniteEtale.fiber v).map f b)) :
    IsIso (pointedEtaleGerm F v B.obj b) := by
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, u, u} A
  let : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} A)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) (forget Ab.{u + 1})
  let Φ := Scheme.pointSmallEtale v
  let er := (sheafToPresheaf X.smallEtaleTopology (Type (u + 1))).mapIso e
  let es := Φ.sheafFiber.mapIso e
  let c := (Φ.sheafFiberCompIso (forget (ModuleCat.{u + 1} A))).app F
  have hset : Function.Bijective
      (Φ.toPresheafFiber B.obj b ((etaleSet A X).obj F).obj) := by
    have hnat := ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_naturality e.hom.hom B.obj b)
    have hc : (fun z ↦ Φ.toPresheafFiber B.obj b ((etaleSet A X).obj F).obj
          ((er.hom.app (op B.obj)) z)) =
        (fun z ↦ es.hom (Φ.toPresheafFiber B.obj b
          ((Scheme.FiniteEtale.toFLC X).obj P).obj.obj z)) := by
      funext z
      exact (hnat z).symm
    have hright := es.toEquiv.bijective.comp (finiteEtale_germ_bijective v P B b heval)
    change Function.Bijective (fun z ↦ es.hom (Φ.toPresheafFiber B.obj b
      ((Scheme.FiniteEtale.toFLC X).obj P).obj.obj z)) at hright
    rw [← hc] at hright
    exact (Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso (er.hom.app (op B.obj)))).mp hright
  have hc : ∀ z : F.obj.obj (op B.obj),
      c.hom (Φ.toPresheafFiber B.obj b ((etaleSet A X).obj F).obj z) =
        pointedEtaleGerm F v B.obj b z := by
    intro z
    exact ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
        (forget (ModuleCat.{u + 1} A)) B.obj b F.obj) z
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h := c.toEquiv.bijective.comp hset
  change Function.Bijective (fun z ↦
    c.hom (Φ.toPresheafFiber B.obj b ((etaleSet A X).obj F).obj z)) at h
  have heq : (fun z ↦ c.hom (Φ.toPresheafFiber B.obj b ((etaleSet A X).obj F).obj z)) =
      (fun z ↦ pointedEtaleGerm F v B.obj b z) := funext hc
  rwa [heq] at h

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
