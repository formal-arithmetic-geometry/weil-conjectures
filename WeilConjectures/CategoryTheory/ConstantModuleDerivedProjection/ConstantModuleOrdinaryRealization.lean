/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleDerivedComparisonData
import all WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleGeometricComparisonData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Ordinary constant-module realization of a geometric inverse image

Source: Stacks Project, Sites, Tag 00YV (6), Modules on Sites, Tag 03EL,
and Cohomology on Sites, Tag 07A4
(blueprint: lem-sfb-constant-module-ordinary-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false
set_option linter.privateModule false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  CategoryTheory.ConstantScalarRestriction.fixedSymmetric
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open SheafOfModules
namespace CategoryTheory.ConstantModuleDerivedProjection
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (max u v)} [CommRing A]

-- Cache the standard sheafification properties before the repeated section calculations.
private instance cachedTypes (J : GrothendieckTopology C) :
    HasSheafify J (Type (max u v)) := inferInstance

private instance cachedComm (J : GrothendieckTopology C) :
    HasSheafify J CommRingCat.{max u v} := inferInstance

private instance cachedRing (J : GrothendieckTopology C) :
    HasSheafify J RingCat.{max u v} := inferInstance

private instance cachedAdd (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{max u v} := inferInstance

private instance cachedFixedSheafify (J : GrothendieckTopology C)
    (A : Type (max u v)) [CommRing A] : HasSheafify J (ModuleCat.{max u v} A) :=
  CategoryTheory.ConstantScalarRestriction.fixedSheafify J A

private instance cachedWeakTypes (J : GrothendieckTopology C) :
    HasWeakSheafify J (Type (max u v)) := inferInstance

private instance cachedWeakComm (J : GrothendieckTopology C) :
    HasWeakSheafify J CommRingCat.{max u v} := inferInstance

private instance cachedWeakRing (J : GrothendieckTopology C) :
    HasWeakSheafify J RingCat.{max u v} := inferInstance

private instance cachedWeakFixed (J : GrothendieckTopology C)
    (A : Type (max u v)) [CommRing A] : HasWeakSheafify J (ModuleCat.{max u v} A) :=
  inferInstance

private instance cachedForgetComm (J : GrothendieckTopology C) :
    J.PreservesSheafification (forget CommRingCat.{max u v}) := inferInstance

private instance cachedForgetRing (J : GrothendieckTopology C) :
    J.PreservesSheafification (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  inferInstance

attribute [local irreducible] presheafToSheaf

private def scalarValue (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (U : Cᵒᵖ) (b : B) : (ring J B).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b

private def scalarSection
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (b : B) :
    (constantSheaf J (Type (max u v))).obj PUnit.{max u v + 1} ⟶
      (sheafCompose J (forget CommRingCat.{max u v})).obj (ring J B) :=
  (constantSheaf J (Type (max u v))).map (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b)) ≫
    (constantCommuteCompose J (forget CommRingCat.{max u v})).inv.app (CommRingCat.of B)

set_option backward.isDefEq.respectTransparency false in
private theorem scalarSection_apply
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (b : B) (U : Cᵒᵖ)
    (t : ((constantSheaf J (Type (max u v))).obj PUnit.{max u v + 1}).obj.obj U) :
    (scalarSection J B b).hom.app U t =
      scalarValue J B U b := by
  dsimp only [scalarValue]
  let P := (Functor.const Cᵒᵖ).obj PUnit.{max u v + 1}
  let : IsIso (toSheafify J P) :=
    isIso_toSheafify J (Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)
  obtain ⟨x, hx⟩ := ((isIso_iff_bijective _).mp
    (inferInstance : IsIso ((toSheafify J P).app U))).2 t
  subst t
  have hn := congrArg (fun f ↦ f.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
      (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b))))
  change _ = ((constantSheaf J (Type (max u v))).map
    (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b))).hom.app U
      ((toSheafify J P).app U x) at hn
  change ((constantCommuteCompose J (forget CommRingCat.{max u v})).inv.app
    (CommRingCat.of B)).hom.app U _ = _
  have hn' : ((constantSheaf J (Type (max u v))).map
      (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b))).hom.app U
        ((toSheafify J P).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b := hn.symm
  apply Eq.trans (congrArg
    (fun z ↦ ((constantCommuteCompose J (forget CommRingCat.{max u v})).inv.app
      (CommRingCat.of B)).hom.app U z) hn')
  have hf := congrArg (fun f ↦ f.app U b)
    (sheafComposeIso_hom_fac J (forget CommRingCat.{max u v})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
  have hconst := toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ (forget CommRingCat.{max u v})).hom.app (CommRingCat.of B))
  have hp := congrArg (fun f ↦ f.app U b) hconst
  dsimp at hp
  change ((sheafifyComposeIso J (forget CommRingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).hom.app U)
      ((((presheafToSheaf J (Type (max u v))).map
        ((Functor.compConstIso Cᵒᵖ (forget CommRingCat.{max u v})).hom.app
          (CommRingCat.of B))).hom.app U)
            ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b)) = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget CommRingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).hom.app U) z) hp.symm).trans hf

set_option backward.isDefEq.respectTransparency false in
private theorem geometric_module_linear (d : GeometricData J K A)
    (N : Modules K A) (T : Sheaf J (Type (max u v)))
    (a : T ⟶ (sheafCompose J (forget CommRingCat.{max u v})).obj (ring J A))
    (x y z : T ⟶ (toSheaf _ ⋙ sheafCompose J
      (forget AddCommGrpCat.{max u v})).obj (d.pushR.obj N))
    (hz : ∀ (U : Cᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((d.pushR.obj N).val.obj U) inferInstance
        (@SMul.smul ((ring J A).obj.obj U) ((d.pushR.obj N).val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) :
    ∀ (U : Dᵒᵖ) (t : (d.inverse.obj T).obj.obj U),
      ((d.geometric.homEquiv T _).symm (z ≫ d.pushUnderlying.hom.app N)).hom.app U t =
        @Add.add (N.val.obj U) inferInstance
          (@SMul.smul ((ring K A).obj.obj U) (N.val.obj U) inferInstance
            ((d.inverse.map a ≫ d.algebraic.ringUnderlying.hom ≫
              (sheafCompose K (forget CommRingCat.{max u v})).map d.scalarIso.hom).hom.app U t)
            (((d.geometric.homEquiv T _).symm
              (x ≫ d.pushUnderlying.hom.app N)).hom.app U t))
          (((d.geometric.homEquiv T _).symm
            (y ≫ d.pushUnderlying.hom.app N)).hom.app U t) := by
  rcases d with ⟨inverse, direct, geometric, inverseRing, algebraic,
    scalarIso, terminalIso, constants, pullR, object_eq, map_eq,
    ringTensor, pushR, ringAdj, pushUnderlying, ringHom, fixed,
    ringed, hi, hd, ha, hm, hmod, hu⟩
  dsimp only at *
  subst inverse
  subst direct
  subst pushR
  have ha' := eq_of_heq ha
  subst geometric
  have hu' := eq_of_heq hu
  subst pushUnderlying
  have hm' := eq_of_heq hm
  intro U t
  have h := ringed.module_linear N T a x y z hz U t
  erw [hm'] at h
  exact h

set_option synthInstance.maxHeartbeats 100000 in
-- Compare the commutative-ring and ring sheafification units.
set_option backward.isDefEq.respectTransparency false in
private theorem restriction_scalar (M : Modules J A) (U : Cᵒᵖ) (a : A)
    (x : M.val.obj U) :
    @SMul.smul A (((restriction J A).obj M).obj.obj U) inferInstance a x =
      scalarValue J A U a • x := by
  dsimp only [scalarValue]
  change ((constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv.app
    (CommRingCat.of A)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app U a) • x = _
  congr 1
  have hf := congrArg (fun f ↦ f.app U a)
    (sheafComposeIso_hom_fac J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
  have hp := congrArg (fun f ↦ f.app U a) (toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).hom.app (CommRingCat.of A)))
  dsimp at hp
  change ((sheafifyComposeIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) _ = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom.app U) z) hp.symm).trans hf

-- Keep chosen sheafification functors behind their naturality APIs.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] scalarValue ring

-- The scalar action can be tested on the binary operation (x,y) ↦ b • x + y.
private theorem pushComparison_operation (d : GeometricData J K A)
    (N : Modules K A) (T : Sheaf J (Type (max u v))) (b : A)
      (x y : T ⟶ (sheafCompose J (forget (ModuleCat.{max u v} A))).obj
        ((restriction J A).obj (d.pushR.obj N))) :
      scalarAdd ((restriction J A).obj (d.pushR.obj N)) T b x y ≫ (d.pushUnderlying.app N ≪≫
        (d.fixedPushUnderlying.app ((restriction K A).obj N)).symm).hom =
        scalarAdd (d.pushA.obj ((restriction K A).obj N)) T b (x ≫ (d.pushUnderlying.app N ≪≫
        (d.fixedPushUnderlying.app ((restriction K A).obj N)).symm).hom)
          (y ≫ (d.pushUnderlying.app N ≪≫
        (d.fixedPushUnderlying.app ((restriction K A).obj N)).symm).hom) := by
  let U := sheafCompose J (forget (ModuleCat.{max u v} A))
  let S := restriction J A
  let H := restriction K A
  let θ (N) : U.obj (S.obj (d.pushR.obj N)) ≅ U.obj (d.pushA.obj (H.obj N)) :=
    d.pushUnderlying.app N ≪≫ (d.fixedPushUnderlying.app (H.obj N)).symm
  apply (cancel_mono (d.fixedPushUnderlying.hom.app (H.obj N))).1
  apply (d.geometric.homEquiv T _).symm.injective
  let a := toConstantUnit J T ≫ scalarSection J A b
  let z := scalarAdd (S.obj (d.pushR.obj N)) T b x y
  have hz (V : Cᵒᵖ) (t : T.obj.obj V) :
      z.hom.app V t = @Add.add ((d.pushR.obj N).val.obj V) inferInstance
        (@SMul.smul _ ((d.pushR.obj N).val.obj V) inferInstance
          (a.hom.app V t) (x.hom.app V t)) (y.hom.app V t) := by
    have hs : a.hom.app V t =
        scalarValue J A V b :=
      scalarSection_apply J A b V _
    erw [hs]
    change @Add.add ((d.pushR.obj N).val.obj V) inferInstance
      (@SMul.smul A (((restriction J A).obj (d.pushR.obj N)).obj.obj V) inferInstance
        b (x.hom.app V t)) (y.hom.app V t) = _
    exact congrArg (fun w : (d.pushR.obj N).val.obj V ↦
      @Add.add ((d.pushR.obj N).val.obj V) inferInstance w (y.hom.app V t))
        (restriction_scalar (d.pushR.obj N) V b (x.hom.app V t))
  have hr := geometric_module_linear d N T a x y z hz
  have hq := d.fixed.linear (H.obj N) T b (x ≫ (θ N).hom) (y ≫ (θ N).hom)
    (scalarAdd (d.pushA.obj (H.obj N)) T b (x ≫ (θ N).hom)
      (y ≫ (θ N).hom)) (fun _ _ ↦ rfl)
  have hc : d.inverse.map (toConstantUnit J T ≫ scalarSection J A b) ≫
      (d.algebraic.ringUnderlying.hom ≫
        (sheafCompose K (forget CommRingCat.{max u v})).map d.scalarIso.hom) =
      d.inverse.map (toConstantUnit J T) ≫ d.terminalIso.hom ≫ scalarSection K A b := by
    erw [Functor.map_comp, Category.assoc]
    with_unfolding_all
      exact congrArg (fun z ↦ d.inverse.map (toConstantUnit J T) ≫ z) (d.constants b)
  ext V t
  have hr' := hr V t
  have hq' := hq V t
  erw [hc] at hr'
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply] at hr'
  have hv := scalarSection_apply K A b V
    ((d.terminalIso.hom.hom.app V)
      ((d.inverse.map (toConstantUnit J T)).hom.app V t))
  have hscl := congrArg (fun c : (ring K A).obj.obj V ↦
    @Add.add (N.val.obj V) inferInstance
      (@SMul.smul ((ring K A).obj.obj V) (N.val.obj V) inferInstance c
        (((d.geometric.homEquiv T _).symm
          (x ≫ d.pushUnderlying.hom.app N)).hom.app V t))
      (((d.geometric.homEquiv T _).symm
        (y ≫ d.pushUnderlying.hom.app N)).hom.app V t)) hv
  have hθ (w : T ⟶ U.obj (S.obj (d.pushR.obj N))) :
      (w ≫ (θ N).hom) ≫ d.fixedPushUnderlying.hom.app (H.obj N) =
        w ≫ d.pushUnderlying.hom.app N := by
    dsimp only [θ, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  erw [hθ x, hθ y] at hq'
  have hs := restriction_scalar N V b
    (((d.geometric.homEquiv T _).symm
      (x ≫ d.pushUnderlying.hom.app N)).hom.app V t)
  have hs' := congrArg (fun w : N.val.obj V ↦ @Add.add (N.val.obj V) inferInstance w
    (((d.geometric.homEquiv T _).symm
      (y ≫ d.pushUnderlying.hom.app N)).hom.app V t)) hs
  have hr'' := hr'.trans (hscl.trans hs'.symm)
  erw [hθ]
  exact hr''.trans hq'.symm

private theorem linearIso_of_scalarAdd (X Y : Fixed J A)
    (θ : (sheafCompose J (forget (ModuleCat.{max u v} A))).obj X ≅
      (sheafCompose J (forget (ModuleCat.{max u v} A))).obj Y)
    (hop : ∀ (T : Sheaf J (Type (max u v))) (b : A)
      (x y : T ⟶ (sheafCompose J (forget (ModuleCat.{max u v} A))).obj X),
      scalarAdd X T b x y ≫ θ.hom = scalarAdd Y T b (x ≫ θ.hom) (y ≫ θ.hom)) :
    ∃ e : X ≅ Y, (sheafCompose J (forget (ModuleCat.{max u v} A))).map e.hom =
      θ.hom := by
  let U := sheafCompose J (forget (ModuleCat.{max u v} A))
  let g V : X.obj.obj V →
      Y.obj.obj V := θ.hom.hom.app V
  have hl V (b : A) (x y : X.obj.obj V) :
      g V (b • x + y) =
        b • g V x + g V y := by
    let A := U.obj X
    have h := hop (MonoidalCategory.tensorObj A A) b (CartesianMonoidalCategory.fst A A)
      (CartesianMonoidalCategory.snd A A)
    exact congrArg (fun f ↦ f.hom.app V (x, y)) h
  have ha V (x y : X.obj.obj V) :
      g V (x + y) =
        g V x + g V y := by
    simpa using hl V 1 x y
  have hz V : g V 0 = 0 := by
    have h := ha V 0 0
    simpa using (add_left_cancel (a := g V 0)
      (by simpa using h.symm :
        g V 0 + g V 0 =
          g V 0 + 0))
  let f : X ⟶ Y :=
    { hom :=
      { app := fun V ↦ ConcreteCategory.ofHom (C := ModuleCat A)
          (show X.obj.obj V →ₗ[A]
              Y.obj.obj V from
          { toFun := g V
            map_add' := ha V
            map_smul' := fun b x ↦ by simpa [hz] using hl V b x 0 })
        naturality := by
          intro V W g
          ext x
          exact congrArg (fun g ↦ g x) (θ.hom.hom.naturality g) } }
  have hf : U.map (f) = θ.hom := rfl
  have : IsIso f := by
    have : IsIso (U.map f) := by erw [hf]; infer_instance
    exact isIso_of_reflects_iso f U
  exact ⟨asIso f, hf⟩

set_option backward.isDefEq.respectTransparency true in
private theorem scalarComparison_fixed (d : GeometricData J K A) :
    ∃ β : d.pushR ⋙ restriction J A ≅ restriction K A ⋙ d.pushA,
      ∀ N, (sheafCompose J (forget (ModuleCat.{max u v} A))).map (β.hom.app N) ≫
        d.fixedPushUnderlying.hom.app ((restriction K A).obj N) =
          d.pushUnderlying.hom.app N := by
  let U := sheafCompose J (forget (ModuleCat.{max u v} A))
  let S := restriction J A
  let H := restriction K A
  let θNat : (d.pushR ⋙ S) ⋙ U ≅ (H ⋙ d.pushA) ⋙ U :=
    d.pushUnderlying ≪≫ (Functor.isoWhiskerLeft H d.fixedPushUnderlying).symm
  let θ (N) := θNat.app N
  have hop := pushComparison_operation d
  choose e he using fun N ↦ linearIso_of_scalarAdd
    (S.obj (d.pushR.obj N)) (d.pushA.obj (H.obj N)) (θ N) (hop N)
  let f N := (e N).hom
  have hf N : U.map (f N) = (θ N).hom := he N
  have hi N : IsIso (f N) := inferInstanceAs (IsIso (e N).hom)
  let β : d.pushR ⋙ S ≅ H ⋙ d.pushA := NatIso.ofComponents
    (fun N ↦ asIso (f N)) (by
      intro N M g
      apply (Functor.map_injective U)
      simp only [Functor.map_comp]
      change U.map (S.map (d.pushR.map g)) ≫ U.map (f M) =
        U.map (f N) ≫ U.map (d.pushA.map (H.map g))
      rw [hf, hf]
      exact θNat.hom.naturality g)
  refine ⟨β, ?_⟩
  intro N
  change U.map (f N) ≫ _ = _
  erw [hf]
  change (d.pushUnderlying.hom.app N ≫ d.fixedPushUnderlying.inv.app (H.obj N)) ≫
    d.fixedPushUnderlying.hom.app (H.obj N) = _
  erw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

attribute [local irreducible] CategoryTheory.sfbSheafTensorStructure
set_option backward.isDefEq.respectTransparency true

private theorem ordinaryIdentification_exists (d : GeometricData J K A) :
    Nonempty (OrdinaryIdentification d) := by
  obtain ⟨β, hβ⟩ := scalarComparison_fixed d
  obtain ⟨α, hHom, _, _⟩ := adjunctionSquare (restriction J A) (restriction K A)
    d.ringAdj d.fixedAdj β
  exact ⟨⟨α, β, hβ, hHom⟩⟩

private def ringedPullback (d : GeometricData J K A) :
    CochainPullback.RingedPullback.{max u v, u, v, u, v} (ring J A) (ring K A) where
  uInv := d.inverse
  uPush := d.direct
  adj := d.geometric
  finiteLimits := d.leftExact
  RI := d.inverseRing
  I := d.algebraic
  coefficient := d.scalarIso.hom
  L := d.pullR
  hobj := d.object_eq
  hmap := d.map_eq
  V := d.pushR
  moduleAdj := d.ringAdj

private def ringedComparison (d : GeometricData J K A) :
    CochainPullback.Comparison.{max u v, u, v, u, v} (ringedPullback d) :=
  SheafOfModules.CochainTensorComparison.ofLanded (ring J A) (ring K A)
    d.inverseRing d.inverse d.algebraic d.scalarIso.hom d.pullR d.object_eq d.ringTensor

private theorem insertion_isIso (d : GeometricData J K A) (M : Modules J A) :
    IsIso (d.ringTensor.q M) := by
  obtain ⟨θ, _, hinv, _⟩ := exists_scalarExtensionRingIso.{u, v, max u v, max u v} d.scalarIso
  let U := toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring K A)) ⋙
      sheafCompose K (forget AddCommGrpCat.{max u v})
  let e := U.mapIso (eqToIso (d.object_eq M)) ≪≫ U.mapIso (θ (d.algebraic.modules.obj M))
  have h : d.ringTensor.q M = e.inv := by
    ext W x
    exact (d.ringTensor.q_one M W x).trans
      (congrArg (fun y ↦ (eqToHom (d.object_eq M).symm).val.app W y)
        (hinv (d.algebraic.modules.obj M) W x).symm)
  rw [h]
  exact ⟨⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩⟩

private abbrev forgetFixed (J : GrothendieckTopology C) (A : Type (max u v)) [CommRing A] :=
  sheafCompose J (forget (ModuleCat.{max u v} A))

private theorem ringUnderlying_exists (d : GeometricData J K A) :
    ∃ e : d.pullR ⋙ restriction K A ⋙ forgetFixed K A ≅
        (restriction J A ⋙ forgetFixed J A) ⋙ d.inverse,
      ∀ M, e.inv.app M = d.algebraic.moduleUnderlying.inv.app M ≫ d.ringTensor.q M := by
  have (M : Modules J A) : IsIso (d.ringTensor.q M) := insertion_isIso d M
  let q : d.algebraic.modules ⋙ toSheaf _ ⋙
      sheafCompose K (forget AddCommGrpCat.{max u v}) ≅
      d.pullR ⋙ toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat.{max u v}) :=
    NatIso.ofComponents (fun M ↦ asIso (d.ringTensor.q M)) (by
      intro M N f
      exact CochainPullback.comparison_q_naturality (ringedPullback d) (ringedComparison d) f)
  let q' : d.pullR ⋙ restriction K A ⋙ forgetFixed K A ≅
      d.algebraic.modules ⋙ toSheaf _ ⋙
        sheafCompose K (forget AddCommGrpCat.{max u v}) := q.symm
  with_unfolding_all exact ⟨q' ≪≫ d.algebraic.moduleUnderlying, fun _ ↦ rfl⟩

private def fixedInsertion (d : GeometricData J K A) :
    forgetFixed J A ⋙ d.inverse ⟶ d.pullA ⋙ forgetFixed K A :=
  ((mateEquiv d.fixedAdj d.geometric).symm d.fixedPushUnderlying.hom).natTrans

private theorem fixedInsertion_hom (d : GeometricData J K A)
    (M : Fixed J A) (N : Fixed K A) (f : d.pullA.obj M ⟶ N) :
    d.geometric.homEquiv _ _ ((fixedInsertion d).app M ≫ (forgetFixed K A).map f) =
      (forgetFixed J A).map (d.fixedAdj.homEquiv M N f) ≫ d.fixedPushUnderlying.hom.app N := by
  have hu := unit_mateEquiv_symm d.fixedAdj d.geometric d.fixedPushUnderlying.hom M
  erw [d.geometric.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu]
  have hn := d.fixedPushUnderlying.hom.naturality f
  change (forgetFixed J A).map (d.pushA.map f) ≫ d.fixedPushUnderlying.hom.app N =
    d.fixedPushUnderlying.hom.app (d.pullA.obj M) ≫
      d.direct.map ((forgetFixed K A).map f) at hn
  erw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]

attribute [local irreducible] fixedInsertion

private theorem fixedInsertion_image (d : GeometricData J K A)
    (o : OrdinaryIdentification d)
    (r : d.pullR ⋙ restriction K A ⋙ forgetFixed K A ≅
      (restriction J A ⋙ forgetFixed J A) ⋙ d.inverse)
    (hr : ∀ M, r.inv.app M = d.algebraic.moduleUnderlying.inv.app M ≫ d.ringTensor.q M)
    (M : Modules J A) :
    (fixedInsertion d).app ((restriction J A).obj M) ≫
        (forgetFixed K A).map (o.left.inv.app M) = r.inv.app M := by
  apply (d.geometric.homEquiv _ _).injective
  rw [fixedInsertion_hom]
  have h := o.hom M (d.pullR.obj M) (𝟙 _)
  erw [Functor.map_id, Category.comp_id] at h
  have h' := congrArg (fun k ↦ (forgetFixed J A).map k ≫
    d.fixedPushUnderlying.hom.app ((restriction K A).obj (d.pullR.obj M))) h
  apply h'.trans
  let f := d.ringAdj.homEquiv M (d.pullR.obj M) (𝟙 _)
  have hu := congrArg (fun k ↦ (forgetFixed J A).map
    ((restriction J A).map f) ≫ k) (o.underlying (d.pullR.obj M))
  have hc : (forgetFixed J A).map
      ((restriction J A).map f ≫ o.right.hom.app (d.pullR.obj M)) ≫
        d.fixedPushUnderlying.hom.app ((restriction K A).obj (d.pullR.obj M)) =
      (forgetFixed J A).map ((restriction J A).map f) ≫
        ((forgetFixed J A).map (o.right.hom.app (d.pullR.obj M)) ≫
          d.fixedPushUnderlying.hom.app ((restriction K A).obj (d.pullR.obj M))) := by
    rw [Functor.map_comp, Category.assoc]
  apply hc.trans (hu.trans ?_)
  have hR := d.ringHom M (d.pullR.obj M) (𝟙 _)
  erw [Functor.map_id, Category.comp_id] at hR
  rw [hr]
  with_unfolding_all exact hR

private theorem fixedInsertion_isIso (d : GeometricData J K A)
    (o : OrdinaryIdentification d) : IsIso (fixedInsertion d) := by
  obtain ⟨r, hr⟩ := ringUnderlying_exists d
  have hi (M : Modules J A) : IsIso ((fixedInsertion d).app ((restriction J A).obj M)) := by
    have h := fixedInsertion_image d o r hr M
    have : IsIso ((fixedInsertion d).app ((restriction J A).obj M) ≫
      (forgetFixed K A).map (o.left.inv.app M)) := by rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((forgetFixed K A).map (o.left.inv.app M))
  let (T : Fixed J A) : IsIso ((fixedInsertion d).app T) := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (restriction J A) T
    let := hi M
    have : IsIso ((forgetFixed J A ⋙ d.inverse).map e.hom ≫
        (fixedInsertion d).app T) := by
      rw [(fixedInsertion d).naturality e.hom]
      infer_instance
    exact IsIso.of_isIso_comp_left ((forgetFixed J A ⋙ d.inverse).map e.hom) _
  exact NatIso.isIso_of_isIso_app _

private theorem fixedInsertion_image_iso (d : GeometricData J K A)
    (o : OrdinaryIdentification d)
    (r : d.pullR ⋙ restriction K A ⋙ forgetFixed K A ≅
      (restriction J A ⋙ forgetFixed J A) ⋙ d.inverse)
    (hr : ∀ M, r.inv.app M = d.algebraic.moduleUnderlying.inv.app M ≫ d.ringTensor.q M)
    (M : Modules J A) (T : Fixed J A) (e : (restriction J A).obj M ≅ T) :
    d.inverse.map ((forgetFixed J A).map e.inv) ≫ r.inv.app M ≫
      (forgetFixed K A).map (o.left.hom.app M ≫ d.pullA.map e.hom) =
        (fixedInsertion d).app T := by
  erw [← fixedInsertion_image d o r hr M, Functor.map_comp,
    Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp]
  have hn := (fixedInsertion d).naturality e.inv
  change d.inverse.map ((forgetFixed J A).map e.inv) ≫
      (fixedInsertion d).app ((restriction J A).obj M) =
    (fixedInsertion d).app T ≫ (forgetFixed K A).map (d.pullA.map e.inv) at hn
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    ← d.pullA.map_comp, e.inv_hom_id, Functor.map_id, Functor.map_id, Category.comp_id]

private def ordinaryCoreOfBraidedInverse {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] [BraidedCategory A] [BraidedCategory B]
    (F : A ⥤ B) (e : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (t : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (hnl : ∀ {X Y : A} (f : X ⟶ Y) Z,
      (t X Z).hom ≫ (F.map f ▷ F.obj Z) = F.map (f ▷ Z) ≫ (t Y Z).hom)
    (hnr : ∀ {X Y : A} Z (f : X ⟶ Y),
      (t Z X).hom ≫ (F.obj Z ◁ F.map f) = F.map (Z ◁ f) ≫ (t Z Y).hom)
    (ha : ∀ X Y Z,
      (t (X ⊗ Y) Z).hom ≫ ((t X Y).hom ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ (t X (Y ⊗ Z)).hom ≫ (F.obj X ◁ (t Y Z).hom))
    (hr : ∀ X, (t X (𝟙_ A)).hom ≫ (F.obj X ◁ e.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom)
    (hb : ∀ X Y, F.map (β_ X Y).hom ≫ (t Y X).hom =
      (t X Y).hom ≫ (β_ (F.obj X) (F.obj Y)).hom) : F.CoreMonoidal := by
  have hl (X : A) : F.map (λ_ X).hom = (t (𝟙_ A) X).hom ≫
      (e.hom ▷ F.obj X) ≫ (λ_ (F.obj X)).hom := by
    calc
      _ = F.map (β_ (𝟙_ A) X).hom ≫ F.map (ρ_ X).hom := by
        rw [← F.map_comp, braiding_rightUnitor]
      _ = F.map (β_ (𝟙_ A) X).hom ≫ (t X (𝟙_ A)).hom ≫
          (F.obj X ◁ e.hom) ≫ (ρ_ (F.obj X)).hom := by rw [hr]
      _ = (t (𝟙_ A) X).hom ≫ (β_ (F.obj (𝟙_ A)) (F.obj X)).hom ≫
          (F.obj X ◁ e.hom) ≫ (ρ_ (F.obj X)).hom := by
        rw [← Category.assoc, ← Category.assoc, hb, Category.assoc, Category.assoc]
      _ = _ := by
        rw [← id_tensorHom, ← tensorHom_id,
          ← BraidedCategory.braiding_naturality_assoc, braiding_rightUnitor]
  refine Functor.CoreMonoidal.mk' e.symm (fun X Y ↦ (t X Y).symm)
    hnl hnr ha ?_ ?_
  · intro X
    apply (cancel_epi (F.map (λ_ X).hom)).1
    rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
    rw [hl X, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  · intro X
    apply (cancel_epi (F.map (ρ_ X).hom)).1
    rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
    rw [← hr X, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl


private theorem monoidalOfBraidedInverse {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] [BraidedCategory A] [BraidedCategory B]
    (F : A ⥤ B) (e : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (t : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (hnl : ∀ {X Y : A} (f : X ⟶ Y) Z,
      (t X Z).hom ≫ (F.map f ▷ F.obj Z) = F.map (f ▷ Z) ≫ (t Y Z).hom)
    (hnr : ∀ {X Y : A} Z (f : X ⟶ Y),
      (t Z X).hom ≫ (F.obj Z ◁ F.map f) = F.map (Z ◁ f) ≫ (t Z Y).hom)
    (ha : ∀ X Y Z,
      (t (X ⊗ Y) Z).hom ≫ ((t X Y).hom ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ (t X (Y ⊗ Z)).hom ≫ (F.obj X ◁ (t Y Z).hom))
    (hr : ∀ X, (t X (𝟙_ A)).hom ≫ (F.obj X ◁ e.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom)
    (hb : ∀ X Y, F.map (β_ X Y).hom ≫ (t Y X).hom =
      (t X Y).hom ≫ (β_ (F.obj X) (F.obj Y)).hom) : ∃ m : F.Monoidal, ∀ X Y,
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F m.toOplaxMonoidal X Y = (t X Y).hom := by
  exact ⟨(ordinaryCoreOfBraidedInverse F e t hnl hnr ha hr hb).toMonoidal, fun _ _ ↦ rfl⟩

private theorem ringedMonoidal_exists
    {R : Sheaf J CommRingCat.{max u v}} {S : Sheaf K CommRingCat.{max u v}}
    (f : CochainPullback.RingedPullback.{max u v, u, v, u, v} R S)
    (k : CochainPullback.Comparison.{max u v, u, v, u, v} f) :
    ∃ m : f.L.Monoidal, ∀ M N,
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ f.L m.toOplaxMonoidal M N =
        (k.mu M N).hom := by
  exact monoidalOfBraidedInverse f.L (CochainPullback.moduleUnit f k) k.mu
    (fun b N ↦ by
      simpa only [Functor.map_id, tensorHom_id] using (k.naturality b (𝟙 N)).symm)
    (fun M b ↦ by
      simpa only [Functor.map_id, id_tensorHom] using (k.naturality (𝟙 M) b).symm)
    (fun M N H ↦ by
      simpa only [tensorHom_id, id_tensorHom] using
        CochainPullback.cochainModuleTensorAssociativity f k M N H)
    (fun M ↦ by
      simpa only [id_tensorHom] using CochainPullback.module_right_unit f k M)
    (CochainPullback.cochainModuleTensorBraiding f k)

private theorem ringMonoidal_exists (d : GeometricData J K A) :
    ∃ m : d.pullR.Monoidal,
      ∀ M N, @Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullR m.toOplaxMonoidal M N =
        (d.ringTensor.mu M N).hom :=
  ringedMonoidal_exists (ringedPullback d) (ringedComparison d)

set_option backward.isDefEq.respectTransparency false in
private theorem fixedPure_map {M M' N N' : Fixed J A}
    (f : M ⟶ M') (g : N ⟶ N') (W : Cᵒᵖ) (x : M.obj.obj W) (y : N.obj.obj W) :
    (f ⊗ₘ g).hom.app W (fixedPure J A M N W x y) =
      fixedPure J A M' N' W (f.hom.app W x) (g.hom.app W y) := by
  let P := presheafToSheaf J (ModuleCat.{max u v} A)
  let : P.Monoidal :=
    (sfbSheafTensorStructure (A := ModuleCat.{max u v} A) J).sheafificationMonoidal
  have hc {T T' : Fixed J A} (h : T ⟶ T') :
      h ≫ (asIso ((sheafificationAdjunction J (ModuleCat A)).counit.app T')).inv =
        (asIso ((sheafificationAdjunction J (ModuleCat A)).counit.app T)).inv ≫
          P.map h.hom := by
    apply (asIso ((sheafificationAdjunction J (ModuleCat A)).counit.app T)).eq_inv_comp.mpr
    rw [← Category.assoc]
    exact (asIso ((sheafificationAdjunction J (ModuleCat A)).counit.app T')).comp_inv_eq.mpr
      ((sheafificationAdjunction J (ModuleCat A)).counit.naturality h).symm
  have hn : (f ⊗ₘ g) ≫ (sfbSheafTensor_comparison J M' N').hom =
      (sfbSheafTensor_comparison J M N).hom ≫ P.map (f.hom ⊗ₘ g.hom) := by
    dsimp only [sfbSheafTensor_comparison]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
      Functor.Monoidal.μIso_hom, Category.assoc]
    erw [← Functor.LaxMonoidal.μ_natural]
    rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    rw [hc f, hc g]
  have hi : (sfbSheafTensor_comparison J M N).inv ≫ (f ⊗ₘ g) =
      P.map (f.hom ⊗ₘ g.hom) ≫ (sfbSheafTensor_comparison J M' N').inv := by
    apply (cancel_epi (sfbSheafTensor_comparison J M N).hom).1
    apply (cancel_mono (sfbSheafTensor_comparison J M' N').hom).1
    simpa only [Iso.hom_inv_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using hn
  have hu := toSheafify_naturality J (f.hom ⊗ₘ g.hom)
  have he := congrArg (fun k ↦ k.hom.app W
    ((toSheafify J (M.obj ⊗ N.obj)).app W (x ⊗ₜ[A] y))) hi
  dsimp only [fixedPure]
  change (f ⊗ₘ g).hom.app W _ = _ at he
  apply he.trans
  have h := congrArg (fun k ↦ k.app W (x ⊗ₜ[A] y)) hu
  exact congrArg ((sfbSheafTensor_comparison J M' N').inv.hom.app W) h.symm

-- Transport through a monoidal equivalence, retaining an explicit tensor formula.
set_option backward.isDefEq.respectTransparency false in
private theorem transport_delta
    {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    [MonoidalCategory X] [MonoidalCategory Y] [MonoidalCategory Z]
    (e : X ≌ Y) [e.functor.Monoidal] (H : X ⥤ Z) [H.Monoidal]
    (F : Y ⥤ Z) (α : H ≅ e.functor ⋙ F) :
    ∃ m : F.Monoidal, ∀ M N,
      let a : e.functor.obj (e.inverse.obj M ⊗ e.inverse.obj N) ≅ M ⊗ N :=
        (Functor.Monoidal.μIso e.functor _ _).symm ≪≫
          (e.counitIso.app M ⊗ᵢ e.counitIso.app N)
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ F m.toOplaxMonoidal M N =
        F.map a.inv ≫ α.inv.app (e.inverse.obj M ⊗ e.inverse.obj N) ≫
          Functor.OplaxMonoidal.δ H _ _ ≫
            ((α.hom.app (e.inverse.obj M) ≫ F.map (e.counitIso.hom.app M)) ⊗ₘ
              (α.hom.app (e.inverse.obj N) ≫ F.map (e.counitIso.hom.app N))) := by
  let := e.inverseMonoidal
  let l : e.inverse ⋙ H ≅ F :=
    Functor.isoWhiskerLeft e.inverse α ≪≫ e.invFunIdAssoc F
  let := Functor.Monoidal.transport l
  refine ⟨inferInstance, ?_⟩
  intro M N
  dsimp only
  let a : e.functor.obj (e.inverse.obj M ⊗ e.inverse.obj N) ≅ M ⊗ N :=
    (Functor.Monoidal.μIso e.functor _ _).symm ≪≫
      (e.counitIso.app M ⊗ᵢ e.counitIso.app N)
  have ha : a.inv = e.counitIso.inv.app (M ⊗ N) ≫
      e.functor.map (Functor.OplaxMonoidal.δ e.inverse M N) := by
    have hh : a.hom = e.functor.map (Functor.LaxMonoidal.μ e.inverse M N) ≫
        e.counitIso.hom.app (M ⊗ N) := by
      exact (e.functor_map_μ_inverse_comp_counitIso_hom_app_tensor M N).symm
    apply (cancel_mono a.hom).1
    rw [a.inv_hom_id, hh]
    simp only [Category.assoc, ← e.functor.map_comp_assoc,
      Functor.Monoidal.δ_μ, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
    rfl
  rw [Functor.Monoidal.transport_δ]
  rw [Functor.OplaxMonoidal.comp_δ]
  simp only [l, Iso.trans_inv, Iso.trans_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Equivalence.invFunIdAssoc_inv_app, Equivalence.invFunIdAssoc_hom_app]
  simp only [Category.assoc]
  rw [← α.inv.naturality_assoc]
  change F.map (e.counitIso.inv.app (M ⊗ N)) ≫
    F.map (e.functor.map (Functor.OplaxMonoidal.δ e.inverse M N)) ≫ _ =
      F.map a.inv ≫ _
  rw [← F.map_comp_assoc, ← ha]

attribute [local irreducible] ringedPullback ringedComparison
  CategoryTheory.ConstantScalarRestriction.fixedMonoidal
  CategoryTheory.ConstantScalarRestriction.restrictionBraided


private theorem fixedTensor_exists (d : GeometricData J K A)
    (o : OrdinaryIdentification d) (E : Fixed J A ⥤ Modules J A)
    (η : 𝟭 (Modules J A) ≅ restriction J A ⋙ E)
    (ε : E ⋙ restriction J A ≅ 𝟭 (Fixed J A))
    (h : ∀ M, (restriction J A).map (η.hom.app M) ≫
      ε.hom.app ((restriction J A).obj M) = 𝟙 _) : Nonempty (FixedTensorData d) := by
  let e : Modules J A ≌ Fixed J A := ⟨restriction J A, E, η, ε, h⟩
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨r, hr⟩ := ringUnderlying_exists d
    let := fixedInsertion_isIso d o
    obtain ⟨mR, hmR⟩ := ringMonoidal_exists d
    let := mR
    let : (restriction J A).Monoidal := (ordinary J A).braided.toMonoidal
    let : e.functor.Monoidal := (ordinary J A).braided.toMonoidal
    let : (restriction K A).Monoidal := (ordinary K A).braided.toMonoidal
    obtain ⟨mF, hmF⟩ := transport_delta e (d.pullR ⋙ restriction K A) d.pullA o.left
    refine ⟨⟨(asIso (fixedInsertion d)).symm,
      fun M N f ↦ (fixedInsertion_hom d M N f).symm, mF, ?_⟩⟩
    intro M N Z x y z hz W t
    let M₀ := e.inverse.obj M
    let N₀ := e.inverse.obj N
    let a : (restriction J A).obj (M₀ ⊗ N₀) ≅ M ⊗ N :=
      (Functor.Monoidal.μIso (restriction J A) M₀ N₀).symm ≪≫
        (e.counitIso.app M ⊗ᵢ e.counitIso.app N)
    let bM : (restriction K A).obj (d.pullR.obj M₀) ≅ d.pullA.obj M :=
      o.left.app M₀ ≪≫ d.pullA.mapIso (e.counitIso.app M)
    let bN : (restriction K A).obj (d.pullR.obj N₀) ≅ d.pullA.obj N :=
      o.left.app N₀ ≪≫ d.pullA.mapIso (e.counitIso.app N)
    let x₀ := x ≫ (forgetFixed J A).map (e.counitIso.inv.app M)
    let y₀ := y ≫ (forgetFixed J A).map (e.counitIso.inv.app N)
    let z₀ := z ≫ (forgetFixed J A).map a.inv
    have hz₀ (V : Cᵒᵖ) (s : Z.obj.obj V) : z₀.hom.app V s =
        ringPure J A M₀ N₀ V (x₀.hom.app V s) (y₀.hom.app V s) := by
      with_unfolding_all
        change (Functor.LaxMonoidal.μ (restriction J A) M₀ N₀).hom.app V
          ((e.counitIso.inv.app M ⊗ₘ e.counitIso.inv.app N).hom.app V
            (z.hom.app V s)) = _
      have hm := fixedPure_map (J := J) (f := e.counitIso.inv.app M)
        (g := e.counitIso.inv.app N) V (x.hom.app V s) (y.hom.app V s)
      have hz' := congrArg
        ((e.counitIso.inv.app M ⊗ₘ e.counitIso.inv.app N).hom.app V) (hz V s)
      apply (congrArg ((Functor.LaxMonoidal.μ (restriction J A) M₀ N₀).hom.app V)
        (hz'.trans hm)).trans
      with_unfolding_all exact (ordinary J A).tensor_inv M₀ N₀ V _ _
    have hg : d.inverse.map z ≫ (fixedInsertion d).app (M ⊗ N) ≫
        (forgetFixed K A).map
          (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullA mF.toOplaxMonoidal M N) =
        d.inverse.map z₀ ≫ r.inv.app (M₀ ⊗ N₀) ≫
          (forgetFixed K A).map ((restriction K A).map (d.ringTensor.mu M₀ N₀).hom) ≫
          (forgetFixed K A).map (Functor.OplaxMonoidal.δ (restriction K A) _ _) ≫
          (forgetFixed K A).map (bM.hom ⊗ₘ bN.hom) := by
      have ht : @Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullA
          mF.toOplaxMonoidal M N = d.pullA.map a.inv ≫
          o.left.inv.app (M₀ ⊗ N₀) ≫
            (restriction K A).map (d.ringTensor.mu M₀ N₀).hom ≫
              Functor.OplaxMonoidal.δ (restriction K A) _ _ ≫
                (bM.hom ⊗ₘ bN.hom) := by
        dsimp only [a, bM, bN, M₀, N₀, Iso.trans_hom, Iso.app_hom,
          Functor.mapIso_hom]
        have h := hmF M N
        dsimp only at h ⊢
        erw [Functor.OplaxMonoidal.comp_δ, hmR] at h
        exact h
      have hn := (fixedInsertion d).naturality a.inv
      change d.inverse.map ((forgetFixed J A).map a.inv) ≫
          (fixedInsertion d).app ((restriction J A).obj (M₀ ⊗ N₀)) =
        (fixedInsertion d).app (M ⊗ N) ≫
          (forgetFixed K A).map (d.pullA.map a.inv) at hn
      have hs : (fixedInsertion d).app (M ⊗ N) ≫
          (forgetFixed K A).map (d.pullA.map a.inv) ≫
            (forgetFixed K A).map (o.left.inv.app (M₀ ⊗ N₀)) =
        d.inverse.map ((forgetFixed J A).map a.inv) ≫ r.inv.app (M₀ ⊗ N₀) := by
        erw [← Category.assoc, ← hn, Category.assoc,
          fixedInsertion_image d o r hr (M₀ ⊗ N₀)]
      let U := forgetFixed K A
      let p := d.pullA.map a.inv
      let q := o.left.inv.app (M₀ ⊗ N₀)
      let q₁ := (restriction K A).map (d.ringTensor.mu M₀ N₀).hom
      let q₂ := Functor.OplaxMonoidal.δ (restriction K A) (d.pullR.obj M₀) (d.pullR.obj N₀)
      let q₃ := bM.hom ⊗ₘ bN.hom
      have hm : U.map (p ≫ q ≫ q₁ ≫ q₂ ≫ q₃) =
          U.map p ≫ U.map q ≫ U.map q₁ ≫ U.map q₂ ≫ U.map q₃ := by
        exact (U.map_comp p _).trans (congrArg (fun k ↦ U.map p ≫ k)
          ((U.map_comp q _).trans (congrArg (fun k ↦ U.map q ≫ k)
            ((U.map_comp q₁ _).trans (congrArg (fun k ↦ U.map q₁ ≫ k)
              (U.map_comp q₂ q₃))))))
      calc
        _ = d.inverse.map z ≫ (fixedInsertion d).app (M ⊗ N) ≫
            U.map (p ≫ q ≫ q₁ ≫ q₂ ≫ q₃) :=
          congrArg (fun k ↦ d.inverse.map z ≫ (fixedInsertion d).app (M ⊗ N) ≫ U.map k) ht
        _ = d.inverse.map z ≫ ((fixedInsertion d).app (M ⊗ N) ≫
            U.map p ≫ U.map q) ≫ U.map q₁ ≫ U.map q₂ ≫ U.map q₃ := by
          rw [hm]
          simp only [Category.assoc]
        _ = d.inverse.map z ≫ (d.inverse.map ((forgetFixed J A).map a.inv) ≫
            r.inv.app (M₀ ⊗ N₀)) ≫ U.map q₁ ≫ U.map q₂ ≫ U.map q₃ :=
          congrArg (fun k ↦ d.inverse.map z ≫ k ≫ U.map q₁ ≫ U.map q₂ ≫ U.map q₃) hs
        _ = _ := by
          dsimp only [z₀]
          rw [d.inverse.map_comp]
          simp only [Category.assoc]
          rfl
    have hx : (d.inverse.map x₀ ≫ r.inv.app M₀ ≫
        (forgetFixed K A).map bM.hom).hom.app W t =
        (d.inverse.map x ≫ (fixedInsertion d).app M).hom.app W t := by
      have h := fixedInsertion_image_iso d o r hr M₀ M (e.counitIso.app M)
      dsimp only [x₀, bM, Iso.trans_hom, Functor.mapIso_hom]
      erw [Functor.map_comp, Category.assoc, h]
    have hy : (d.inverse.map y₀ ≫ r.inv.app N₀ ≫
        (forgetFixed K A).map bN.hom).hom.app W t =
        (d.inverse.map y ≫ (fixedInsertion d).app N).hom.app W t := by
      have h := fixedInsertion_image_iso d o r hr N₀ N (e.counitIso.app N)
      dsimp only [y₀, bN, Iso.trans_hom, Functor.mapIso_hom]
      erw [Functor.map_comp, Category.assoc, h]
    have hp := d.ringTensor.pure M₀ N₀ Z x₀ y₀ z₀ hz₀ W t
    have hp' : (d.inverse.map z₀ ≫ r.inv.app (M₀ ⊗ N₀) ≫
        (forgetFixed K A).map ((restriction K A).map (d.ringTensor.mu M₀ N₀).hom)).hom.app W t =
        ringPure K A (d.pullR.obj M₀) (d.pullR.obj N₀) W
          ((d.inverse.map x₀ ≫ r.inv.app M₀).hom.app W t)
          ((d.inverse.map y₀ ≫ r.inv.app N₀).hom.app W t) := by
      have h₁ := congrArg (fun q ↦ (d.inverse.map z₀ ≫ q ≫
        (forgetFixed K A).map ((restriction K A).map
          (d.ringTensor.mu M₀ N₀).hom)).hom.app W t) (hr (M₀ ⊗ N₀))
      have h₂ := congrArg (fun q ↦ (d.inverse.map x₀ ≫ q).hom.app W t) (hr M₀)
      have h₃ := congrArg (fun q ↦ (d.inverse.map y₀ ≫ q).hom.app W t) (hr N₀)
      exact h₁.trans (hp.trans (congrArg₂
        (ringPure K A (d.pullR.obj M₀) (d.pullR.obj N₀) W) h₂ h₃).symm)
    change (d.inverse.map z ≫ (fixedInsertion d).app (M ⊗ N) ≫ _).hom.app W t = _
    apply (congrArg (fun f ↦ f.hom.app W t) hg).trans
    change (bM.hom ⊗ₘ bN.hom).hom.app W
      ((Functor.OplaxMonoidal.δ (restriction K A) _ _).hom.app W
        ((d.inverse.map z₀ ≫ r.inv.app (M₀ ⊗ N₀) ≫
          (forgetFixed K A).map ((restriction K A).map
            (d.ringTensor.mu M₀ N₀).hom)).hom.app W t)) = _
    apply (congrArg (fun w ↦ (bM.hom ⊗ₘ bN.hom).hom.app W
      ((Functor.OplaxMonoidal.δ (restriction K A) _ _).hom.app W w)) hp').trans
    have ht := (ordinary K A).tensor_hom (d.pullR.obj M₀) (d.pullR.obj N₀) W
      ((d.inverse.map x₀ ≫ r.inv.app M₀).hom.app W t)
      ((d.inverse.map y₀ ≫ r.inv.app N₀).hom.app W t)
    with_unfolding_all
      apply (congrArg ((bM.hom ⊗ₘ bN.hom).hom.app W) ht).trans
    exact (fixedPure_map bM.hom bN.hom W _ _).trans
      (congrArg₂ (fixedPure K A (d.pullA.obj M) (d.pullA.obj N) W) hx hy)

-- Preserve the original existential binder, whose witness is intentionally independent
-- of the second conjunct in the statement.
set_option linter.unusedVariables false in
/-- The ordinary scalar comparison and normalized tensor inverse image.
Source: Stacks Tags 00YV (6), 03EL and 07A4
(blueprint: lem-sfb-constant-module-ordinary-realization).

Proof: the constant-section equation identifies the scalar action of the ringed direct
image with the fixed-scalar action. The identity on its underlying sheaf is therefore
linear and gives the natural right comparison. Scalar restriction is an exact equivalence;
transporting the ringed adjunction and using uniqueness of left adjoints gives the left
comparison and its Hom equation. Its underlying inverse-image isomorphism is obtained
from the algebraic inverse image and scalar extension along the specified ring isomorphism.
This identifies the fixed inverse image with the geometric inverse image on underlying
sheaves. Tensor the scalar-extension units: on generalized pure tensors the map
sends the inverse image of x tensor y to the tensor of their inverse images. The tensor
universal property and sheafification extend this to the tensor isomorphism. Associativity,
the two unit laws and naturality hold on pure tensors and hence on all sheaves. The
adjunction Hom equation on underlying sheaves follows from the given normalized ringed
Hom equation. These give exactly FixedTensorData, without requiring enough points,
a nonzero ring, or boundedness. -/
theorem constant_module_ordinary_realization (d : GeometricData J K A) :
    ∃ o : OrdinaryIdentification d, Nonempty (FixedTensorData d) := by
  obtain ⟨_o⟩ := ordinaryIdentification_exists d
  let e := (restriction J A).asEquivalence
  exact ⟨_o, fixedTensor_exists d _o e.inverse e.unitIso e.counitIso
    e.functor_unitIso_comp⟩

end CategoryTheory.ConstantModuleDerivedProjection
