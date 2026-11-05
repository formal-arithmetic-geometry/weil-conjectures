/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-!
# Scalar extension of a localized inverse-image constant model

Source: Stacks Project, Tags 03EL, 0GMW and 093V
(blueprint: lem-sf-finite-field-local-tensor-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace FiniteFieldTensor

open SheafOfModules

set_option backward.isDefEq.respectTransparency false
open scoped ChangeOfRings

-- The tensor adjunction argument from ModulePullbackPushforwardAdjunction,
-- with the independent object and morphism universes of the pro-etale site.
private abbrev ringSheaf {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (R : Sheaf J CommRingCat.{u + 1}) :=
  (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

private noncomputable abbrev restriction
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

private noncomputable def tensorPresheafFunctor
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :
    SheafOfModules.{u + 1} (ringSheaf A) ⥤ PresheafOfModules.{u + 1} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{u, u + 1, u + 1} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶
      changeOfRingsPresheaf.{u, u + 1, u + 1} c N from
    { app := fun W ↦
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{u, u + 1, u + 1} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :
    SheafOfModules.{u + 1} (ringSheaf A) ⥤ SheafOfModules.{u + 1} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def overRingMap
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A S : Sheaf J CommRingCat.{u + 1}} (a : A ⟶ S) (V : C) :
    A.over V ⟶ S.over V :=
  (J.overPullback CommRingCat.{u + 1} V).map a

private noncomputable def overRestrictionIso
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    {A S : Sheaf J CommRingCat.{u + 1}} (a : A ⟶ S) (V : C) :
    pushforward (SheafOfModules.pushforwardOver (R := ringSheaf S) V) ⋙
        restriction a ≅
      restriction (overRingMap a V) ⋙
        pushforward (SheafOfModules.pushforwardOver (R := ringSheaf A) V) := by
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)) ?_
  · let P := (((pushforward (SheafOfModules.pushforwardOver (R := ringSheaf S) V) ⋙
        restriction a).obj M).val.obj U)
    let Q := (((restriction (overRingMap a V) ⋙
        pushforward (SheafOfModules.pushforwardOver (R := ringSheaf A) V)).obj M).val.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[A.obj.obj U] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r m ↦ ?_ }).toModuleIso
    change S.obj.map (Limits.prod.snd : V ⨯ U.unop ⟶ U.unop).op ((a.hom.app U).hom r) •
        (show M.val.obj ((Over.star V).op.obj U) from m) =
      ((a.hom.app ((Over.forget V).op.obj ((Over.star V).op.obj U))).hom
        (A.obj.map (Limits.prod.snd : V ⨯ U.unop ⟶ U.unop).op r)) •
        (show M.val.obj ((Over.star V).op.obj U) from m)
    exact congrArg (fun b ↦ b •
      (show M.val.obj ((Over.star V).op.obj U) from m))
      (ConcreteCategory.congr_hom
        (a.hom.naturality (Limits.prod.snd : V ⨯ U.unop ⟶ U.unop).op).symm r)
  · intro U W h
    ext m
    rfl
  · intro M N h
    ext U m
    rfl

private def constantPresheaf
    {C : Type (u + 1)} [Category.{u} C] (B : Type (u + 1)) [CommRing B] :
    ModuleCat.{u + 1} B ⥤
      PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of B)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ 𝟙 M }
  map h := { app := fun _ ↦ h }

private noncomputable def constantPresheafHomEquiv
    {C : Type (u + 1)} [Category.{u} C] [HasTerminal C]
    (B : Type (u + 1)) [CommRing B] (M : ModuleCat.{u + 1} B)
    (P : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :
    ((constantPresheaf B).obj M ⟶ P) ≃ (M ⟶ P.obj (op (⊤_ C))) where
  toFun h := h.app _
  invFun h :=
    { app := fun U ↦ h ≫ P.map (terminal.from U.unop).op
      naturality := by
        intro U W a
        ext m
        change P.map (terminal.from W.unop).op (h m) =
          P.map a (P.map (terminal.from U.unop).op (h m))
        rw [← P.map_comp_apply]
        have he : (terminal.from W.unop).op = (terminal.from U.unop).op ≫ a :=
          Subsingleton.elim _ _
        rw [he] }
  left_inv h := by
    ext U m
    have hh := PresheafOfModules.naturality_apply h (terminal.from U.unop).op m
    exact hh.symm
  right_inv h := by
    ext m
    change P.map (terminal.from (⊤_ C)).op (h m) = h m
    have he : terminal.from (⊤_ C) = 𝟙 (⊤_ C) := Subsingleton.elim _ _
    rw [he, op_id]
    exact ConcreteCategory.congr_hom (P.presheaf.map_id _) (h m)

private noncomputable def constantPresheafAdjunction
    {C : Type (u + 1)} [Category.{u} C] [HasTerminal C]
    (B : Type (u + 1)) [CommRing B] :
    constantPresheaf (C := C) B ⊣
      PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of B)) (op (⊤_ C)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv B
      homEquiv_naturality_left_symm := by intros; ext U m; rfl
      homEquiv_naturality_right := by intros; rfl }

private noncomputable def constantSections
    (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    pbcModules Y (adicLisseConstantRing Y B) ⥤ ModuleCat.{u + 1} B :=
  SheafOfModules.forget (adicLisseRing Y B) ⋙
    PresheafOfModules.restrictScalars (adicLisseConstantUnit Y B) ⋙
      PresheafOfModules.evaluation.{u + 1} ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B))
        (op (⊤_ Y.ProEt))

private noncomputable def constantAdjunction
    (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    adicLisseConstantModules Y B ⊣ constantSections Y B :=
  (constantPresheafAdjunction (C := Y.ProEt) B).comp
    (PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit Y B))

private noncomputable def fieldRingMap
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    adicLisseConstantRing Y (ULift.{u + 1} k) ⟶
      adicLisseConstantRing Y (ULift.{u + 1} k') :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))

private theorem fieldUnit_naturality
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    adicLisseConstantUnit Y (ULift.{u + 1} k) ≫
        ((adicLisseForget Y).map (fieldRingMap Y f)).hom =
      Functor.whiskerRight
        ((Functor.const Y.ProEtᵒᵖ).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))
        (forget₂ CommRingCat RingCat) ≫ adicLisseConstantUnit Y (ULift.{u + 1} k') := by
  ext U b
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).symm U) b

private noncomputable def restrictionSectionsIso
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    pbcRestrict (fieldRingMap Y f) ⋙ constantSections Y (ULift.{u + 1} k) ≅
      constantSections Y (ULift.{u + 1} k') ⋙
        ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} f) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let P := (((pbcRestrict (fieldRingMap Y f) ⋙
        constantSections Y (ULift.{u + 1} k)).obj M))
    let Q := (((constantSections Y (ULift.{u + 1} k') ⋙
        ModuleCat.restrictScalars.{u + 1}
          (RingHom.ulift.{u + 1, u + 1} f)).obj M))
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[ULift.{u + 1} k] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    change (((fieldRingMap Y f).hom.app (op (⊤_ Y.ProEt))).hom
        (((adicLisseConstantUnit Y (ULift.{u + 1} k)).app (op (⊤_ Y.ProEt))).hom b)) •
          (show M.val.obj (op (⊤_ Y.ProEt)) from m) =
      (((adicLisseConstantUnit Y (ULift.{u + 1} k')).app (op (⊤_ Y.ProEt))).hom
        ((RingHom.ulift f) b)) •
          (show M.val.obj (op (⊤_ Y.ProEt)) from m)
    exact congrArg (fun a ↦ a • (show M.val.obj (op (⊤_ Y.ProEt)) from m))
      (ConcreteCategory.congr_hom (congr_app (fieldUnit_naturality Y f) (op (⊤_ Y.ProEt))) b)
  · intro M N h
    ext m
    rfl

private noncomputable def constantExtensionIso
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    adicLisseConstantModules Y (ULift.{u + 1} k) ⋙ pbcExtend (fieldRingMap Y f) ≅
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (RingHom.ulift.{u + 1, u + 1} f) ⋙
          adicLisseConstantModules Y (ULift.{u + 1} k') :=
  ((constantAdjunction Y (ULift.{u + 1} k)).comp
    (pbcScalarAdjunction (fieldRingMap Y f))).leftAdjointUniq
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (RingHom.ulift.{u + 1, u + 1} f)).comp
          (constantAdjunction Y (ULift.{u + 1} k'))).ofNatIsoRight
            (restrictionSectionsIso Y f).symm)

end FiniteFieldTensor

private noncomputable def inverseImageRestrictionIso
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (a : R ⟶ S) :
    proEtaleRingModuleDirectImage g S
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj S) (Iso.refl _) ⋙
        pbcRestrict a ≅
      pbcRestrict ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a) ⋙
        proEtaleRingModuleDirectImage g R
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R) (Iso.refl _) := by
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)) ?_
  · let P := (((proEtaleRingModuleDirectImage g S
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj S) (Iso.refl _) ⋙
        pbcRestrict a).obj M).val.obj U)
    let Q := (((pbcRestrict ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a) ⋙
        proEtaleRingModuleDirectImage g R
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R)
          (Iso.refl _)).obj M).val.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[R.obj.obj U] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r m ↦ ?_ }).toModuleIso
    change (((proEtaleRingDirectImageMap g S _ (Iso.refl _)).hom.app U).hom
        ((a.hom.app U).hom r)) •
          (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m) =
      ((((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a).hom.app
        ((proEtaleBaseChange g).op.obj U)).hom
          (((proEtaleRingDirectImageMap g R _ (Iso.refl _)).hom.app U).hom r)) •
          (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m)
    simp only [proEtaleRingDirectImageMap]
    exact congrArg (fun b ↦ b •
        (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m))
      (ConcreteCategory.congr_hom
        (congrArg (fun b ↦ b.hom.app U)
          ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality a)) r)
  · intro U V h
    ext m
    rfl
  · intro M N h
    ext U m
    rfl

private noncomputable def inverseImageExtensionIso
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (a : R ⟶ S) :
    pbcExtend a ⋙ proEtaleModuleInverseImage g S ≅
      proEtaleModuleInverseImage g R ⋙
        pbcExtend ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a) :=
  (conjugateIsoEquiv
    ((proEtaleModuleInverseImageAdjunction g R).comp
      (pbcScalarAdjunction ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a)))
    ((pbcScalarAdjunction a).comp (proEtaleModuleInverseImageAdjunction g S))).symm
      (inverseImageRestrictionIso g a).symm

end AlgebraicGeometry.Scheme
