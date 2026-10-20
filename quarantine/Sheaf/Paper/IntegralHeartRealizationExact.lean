/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module
public import Sheaf.Paper.IntegralHeartLocalModel
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
/-!
# Exactness and finite free terms of integral scalar realization

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart,
the first two sentences of the integral-heart-dualizable proof.
(blueprint: lem-integral-heart-realization-exact)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale
section Unit
variable {A B : Type w} [CommRing A] [CommRing B] (φ : A →+* B)
set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def scalarUnitIso :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of A A) ≅ ModuleCat.of B B := by
  letI : Algebra A B := φ.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem scalarUnitIso_hom_tmul (b : B) (a : A) :
    (scalarUnitIso φ).hom (b ⊗ₜ[A, φ] a) = b * φ a := by
  change φ a * b = b * φ a
  exact mul_comm _ _
set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem scalarUnitIso_inv_apply (b : B) :
    (scalarUnitIso φ).inv b = b ⊗ₜ[A, φ] (1 : A) := rfl

end Unit
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open CategoryTheory.InternalAbelianSheafModule

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def continuousSectionEquiv (O : Type) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (U : Profinite.{u}ᵒᵖ) :
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingObj.{u} O)).obj.obj U ≃+* ULift.{u + 1} C(U.unop, O) where
  toFun := fun f ↦ f
  invFun := fun f ↦ f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' f g := by
    let R := Profinite.continuousMapRingObj.{u} O
    let J := coherentTopology Profinite.{u}
    let F := sheafToPresheaf J Ab.{u + 1}
    let : MonObj R.obj := (Profinite.continuousMapRingSheaf.{u} O).obj.monObjCompForget₂
    change ((Functor.LaxMonoidal.μ F R R ≫ F.map μ[R]).app U).hom
      (f ⊗ₜ[ℤ] g) = (μ[R.obj].app U).hom (f ⊗ₜ[ℤ] g)
    rw [Sheaf.μ_comp_map_mul]
    rfl

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem flat_of_targetIso {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]
    (e : B ≃+* D) (f : A →+* B) (h : (e.toRingHom.comp f).Flat) : f.Flat := by
  have h' := h.comp (RingHom.Flat.of_bijective (f := e.symm.toRingHom) e.symm.bijective)
  have he : e.symm.toRingHom.comp (e.toRingHom.comp f) = f := by
    ext a
    exact e.symm_apply_apply (f a)
  rwa [he] at h'

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def continuousConstantMap (O : Type) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (U : Profinite.{u}ᵒᵖ) :
    ULift.{u + 1} O →+* ULift.{u + 1} C(U.unop, O) where
  toFun a := ULift.up (ContinuousMap.const _ a.down)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
set_option linter.style.haveILetI false in
-- Inline the algebra instance to keep the sectionwise torsion-free proof small.
private theorem continuousConstantMap_flat (O : Type) [CommRing O] [IsDomain O]
    [TopologicalSpace O] [IsTopologicalRing O]
    [IsPrincipalIdealRing (ULift.{u + 1} O)] (U : Profinite.{u}ᵒᵖ) :
    (continuousConstantMap O U).Flat := by
  let : IsDomain (ULift.{u + 1} O) :=
    MulEquiv.isDomain O (ULift.ringEquiv : ULift.{u + 1} O ≃+* O).toMulEquiv
  let φ := continuousConstantMap O U
  letI : Algebra (ULift.{u + 1} O) (ULift.{u + 1} C(U.unop, O)) := φ.toAlgebra
  have : Module.IsTorsionFree (ULift.{u + 1} O) (ULift.{u + 1} C(U.unop, O)) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r f h
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    apply ULift.ext
    ext t
    have ht := congrArg (fun g : ULift.{u + 1} C(U.unop, O) ↦ g.down t) h
    change r.down * f.down t = 0 at ht
    exact (mul_eq_zero.mp ht).resolve_left (fun h ↦ hr (ULift.ext _ _ h))
  change Module.Flat (ULift.{u + 1} O) (ULift.{u + 1} C(U.unop, O))
  infer_instance

section SectionUnit
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max u v, w}] [HasSheafify J AddCommGrpCat.{w}]
  [(J.W (A := AddCommGrpCat.{w})).IsMonoidal]
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def sectionRegularIso (R : Sheaf J AddCommGrpCat.{w})
    [MonObj R] [IsCommMonObj R] :
    PresheafOfModules.unit ((sectionRingSheaf J R).obj ⋙ forget₂ CommRingCat RingCat) ≅
      ((sectionModuleFunctor J R).obj (Mod.regular R)).val := by
  refine PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext m
    rfl
  · intro U V f
    ext
    rfl
end SectionUnit

section Raw
variable {C : Type u} [Category.{v} C] {A : Type w} [CommRing A]
  (R : Cᵒᵖ ⥤ CommRingCat.{w})
  (α : (Functor.const Cᵒᵖ).obj (CommRingCat.of A) ⟶ R)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawRestriction (M : ModuleCat.{w} A) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (ModuleCat.extendScalars (α.app U).hom).obj M ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj
        ((ModuleCat.extendScalars (α.app V).hom).obj M) := by
  let mU : Module A (R.obj U) := Module.compHom _ (α.app U).hom
  let mV : Module A (R.obj V) := Module.compHom _ (α.app V).hom
  letI : Module (R.obj U) (TensorProduct A (R.obj U) M) :=
    ((ModuleCat.extendScalars (α.app U).hom).obj M).isModule
  letI : Module (R.obj V) (TensorProduct A (R.obj V) M) :=
    ((ModuleCat.extendScalars (α.app V).hom).obj M).isModule
  let ρ : R.obj U →ₗ[A] R.obj V :=
    { toFun := (R.map f).hom
      map_add' := (R.map f).hom.map_add
      map_smul' := by
        intro a s
        change R.map f (α.app U a * s) = α.app V a * R.map f s
        rw [map_mul]
        congr 1
        exact ConcreteCategory.congr_hom (α.naturality f).symm a }
  refine ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      ((ModuleCat.extendScalars (α.app V).hom).obj M))
    { toFun := TensorProduct.map ρ (LinearMap.id : M →ₗ[A] M)
      map_add' := (TensorProduct.map ρ (LinearMap.id : M →ₗ[A] M)).map_add
      map_smul' := ?_ }
  intro s z
  change TensorProduct.map ρ (LinearMap.id : M →ₗ[A] M) (s • z) =
    (R.map f s) • TensorProduct.map ρ (LinearMap.id : M →ₗ[A] M) z
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul t m =>
    change R.obj U at t
    change R.map f (s * t) ⊗ₜ[A, (α.app V).hom] m =
      (R.map f s * R.map f t) ⊗ₜ[A, (α.app V).hom] m
    rw [map_mul]
  | add x y hx hy =>
    rw [smul_add, map_add, map_add, hx, hy, smul_add]

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem rawRestriction_tmul (M : ModuleCat.{w} A) {U V : Cᵒᵖ}
    (f : U ⟶ V) (s : R.obj U) (m : M) :
    rawRestriction R α M f (s ⊗ₜ[A, (α.app U).hom] m) =
      R.map f s ⊗ₜ[A, (α.app V).hom] m := rfl

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawObj (M : ModuleCat.{w} A) :
    PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) where
  obj U := (ModuleCat.extendScalars (α.app U).hom).obj M
  map f := rawRestriction R α M f
  map_id U := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change R.map (𝟙 U) (1 : R.obj U) ⊗ₜ[A, (α.app U).hom] m =
      (1 : R.obj U) ⊗ₜ[A, (α.app U).hom] m
    rw [map_one]
  map_comp {U V W} f g := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change R.map (f ≫ g) 1 ⊗ₜ[A, (α.app W).hom] m =
      R.map g (R.map f 1) ⊗ₜ[A, (α.app W).hom] m
    rw [map_one, map_one, map_one]

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawFunctor : ModuleCat.{w} A ⥤
    PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) where
  obj := rawObj R α
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars (α.app U).hom).map f
      naturality := by
        intro U V g
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        change R.map g 1 ⊗ₜ[A, (α.app V).hom] f m =
          R.map g 1 ⊗ₜ[A, (α.app V).hom] f m
        rfl }
  map_id _ := by
    ext U : 1
    exact (ModuleCat.extendScalars (α.app U).hom).map_id _
  map_comp _ _ := by
    ext U : 1
    exact (ModuleCat.extendScalars (α.app U).hom).map_comp _ _
set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawToRestriction (M : ModuleCat.{w} A)
    (H : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    (f : (rawObj R α M) ⟶ H) :
    ({ obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id } :
      PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of A))) ⟶
    (PresheafOfModules.restrictScalars
      (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj H where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
    (α.app U).hom (f.app U)
  naturality := by
    intro U V i
    ext m
    have h := PresheafOfModules.naturality_apply f i
      ((1 : R.obj U) ⊗ₜ[A, (α.app U).hom] m)
    change f.app V (R.map i 1 ⊗ₜ[A, (α.app V).hom] m) = _ at h
    rw [map_one] at h
    exact h

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawFromRestriction (M : ModuleCat.{w} A)
    (H : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat))
    (g : ({ obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id } :
      PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of A))) ⟶
    (PresheafOfModules.restrictScalars
      (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj H) :
    rawObj R α M ⟶ H where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (X := M) (Y := H.obj U) (α.app U).hom (g.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (X := M) (Y := H.obj V) (α.app V).hom (g.app V) (R.map i 1 ⊗ₜ[A, (α.app V).hom] m) =
      H.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (X := M) (Y := H.obj U) (α.app U).hom (g.app U) ((1 : R.obj U) ⊗ₜ[A, (α.app U).hom] m))
    rw [map_one]
    have atOne (U : Cᵒᵖ) (n : M) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (X := M) (Y := H.obj U) (α.app U).hom (g.app U)
          ((1 : R.obj U) ⊗ₜ[A, (α.app U).hom] n) = g.app U n := by
      exact congrArg (fun (f : M ⟶ (ModuleCat.restrictScalars (α.app U).hom).obj (H.obj U)) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
          (X := M) (Y := H.obj U) (α.app U).hom).apply_symm_apply
          (g.app U))
    rw [atOne, atOne]
    exact PresheafOfModules.naturality_apply g i m

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawHomEquiv (M : ModuleCat.{w} A)
    (H : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    (rawObj R α M ⟶ H) ≃
      (({ obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id } :
        PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of A))) ⟶
      (PresheafOfModules.restrictScalars
        (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj H) where
  toFun := rawToRestriction R α M H
  invFun := rawFromRestriction R α M H
  left_inv f := by
    ext U : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom).symm_apply_apply _
  right_inv g := by
    ext U : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
          (X := M) (Y := H.obj U) (α.app U).hom).apply_symm_apply _
set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem raw_preservesFiniteLimits (h : ∀ U, (α.app U).hom.Flat) :
    PreservesFiniteLimits (rawFunctor R α) where
  preservesFiniteLimits _J _ _ := ⟨⟨fun hc ↦ ⟨
    PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun U ↦ by
      have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (h U)
      exact isLimitOfPreserves (ModuleCat.extendScalars (α.app U).hom) hc)⟩⟩⟩

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem raw_preservesFiniteColimits :
    PreservesFiniteColimits (rawFunctor R α) where
  preservesFiniteColimits _J _ _ := ⟨⟨fun hc ↦ ⟨
    PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun U ↦
      isColimitOfPreserves (ModuleCat.extendScalars (α.app U).hom) hc)⟩⟩⟩

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawUnitIso :
    rawObj R α (ModuleCat.of A A) ≅
      PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat) where
  hom :=
    { app := fun U ↦ (scalarUnitIso (A := A) (B := R.obj U) (α.app U).hom).hom
      naturality := by
        intro U V f
        apply ModuleCat.ExtendScalars.hom_ext
        intro a
        change A at a
        change (scalarUnitIso (A := A) (B := R.obj V) (α.app V).hom).hom
          (rawRestriction R α (ModuleCat.of A A) f ((1 : R.obj U) ⊗ₜ[A, (α.app U).hom] a)) =
          R.map f ((scalarUnitIso (A := A) (B := R.obj U) (α.app U).hom).hom
            ((1 : R.obj U) ⊗ₜ[A, (α.app U).hom] a))
        rw [rawRestriction_tmul, scalarUnitIso_hom_tmul, scalarUnitIso_hom_tmul,
          map_one, _root_.one_mul, _root_.one_mul]
        exact ConcreteCategory.congr_hom (α.naturality f) a }
  inv :=
    { app := fun U ↦ (scalarUnitIso (A := A) (B := R.obj U) (α.app U).hom).inv
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change R.obj U at a
        change (scalarUnitIso (A := A) (B := R.obj V) (α.app V).hom).inv (R.map f a) =
          rawRestriction R α (ModuleCat.of A A) f
            ((scalarUnitIso (A := A) (B := R.obj U) (α.app U).hom).inv a)
        rw [scalarUnitIso_inv_apply, scalarUnitIso_inv_apply]
        exact (rawRestriction_tmul R α (ModuleCat.of A A) f a 1).symm }
  hom_inv_id := by
    ext U : 1
    exact (scalarUnitIso (A := A) (B := R.obj U) (α.app U).hom).hom_inv_id
  inv_hom_id := by
    ext U : 1
    exact (scalarUnitIso (A := A) (B := R.obj U) (α.app U).hom).inv_hom_id

end Raw

attribute [local irreducible] PresheafOfModules.sheafification
section Extension
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R S : Sheaf J CommRingCat.{w}} (α : R ⟶ S)
  (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  (N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def identitySheafificationIso :
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).obj N.val ≅ N :=
  asIso ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).counit.app N)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def extensionToRestriction
    (f : SheafOfModules.changeOfRingsPresheafOfUniverses.{v, u, w, w} α M ⟶ N.val) :
    M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N where
  val :=
    { app := fun U ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (α.hom.app U).hom (f.app U)
      naturality := by
        intro U V i
        ext m
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] m)
        change f.app V (SheafOfModules.changeOfRingsMapOfUniverses.{v, u, w, w} α M i _) = _ at h
        rw [SheafOfModules.changeOfRingsMap_tmulOfUniverses, map_one] at h
        exact h }

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def extensionFromRestriction
    (g : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :
    SheafOfModules.changeOfRingsPresheafOfUniverses.{v, u, w, w} α M ⟶ N.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (α.hom.app U).hom (g.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (α.hom.app V).hom (g.val.app V)
      (SheafOfModules.changeOfRingsMapOfUniverses.{v, u, w, w} α M i _) = _
    rw [SheafOfModules.changeOfRingsMap_tmulOfUniverses, map_one]
    have atOne (U : Cᵒᵖ) (m : M.val.obj U) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (α.hom.app U).hom (g.val.app U)
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] m) = g.val.app U m := by
      exact congrArg (fun (f : M.val.obj U ⟶ (ModuleCat.restrictScalars
          (α.hom.app U).hom).obj (N.val.obj U)) ↦ f m)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
          (α.hom.app U).hom).apply_symm_apply (g.val.app U))
    rw [atOne]
    change _ = N.val.map i
      (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (α.hom.app U).hom (g.val.app U)
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] m))
    rw [atOne]
    exact PresheafOfModules.naturality_apply g.val i m

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def extensionHomEquiv :
    (SheafOfModules.changeOfRingsOfUniverses.{v, u, w, w} α M ⟶ N) ≃
      (M ⟶ (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).trans
    { toFun := extensionToRestriction α M N
      invFun := extensionFromRestriction α M N
      left_inv := fun f ↦ by
        ext U : 1
        exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
          (α.hom.app U).hom).symm_apply_apply _
      right_inv := fun g ↦ by
        ext U : 2
        exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
          (α.hom.app U).hom).apply_symm_apply _ }

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem extensionHomEquiv_comp
    {N' : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)}
    (f : SheafOfModules.changeOfRingsOfUniverses.{v, u, w, w} α M ⟶ N) (g : N ⟶ N') :
    extensionHomEquiv α M N' (f ≫ g) = extensionHomEquiv α M N f ≫
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).map g := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv_naturality_right
      (X := SheafOfModules.changeOfRingsPresheafOfUniverses.{v, u, w, w} α M) f g
  ext U x
  exact congrArg (fun k : SheafOfModules.changeOfRingsPresheafOfUniverses.{v, u, w, w} α M ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).obj N'.val ↦
      k.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) h

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem extensionHomEquiv_precomp
    {M' : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (m : M' ⟶ M) (f : SheafOfModules.changeOfRingsOfUniverses.{v, u, w, w} α M ⟶ N) :
    extensionHomEquiv α M' N (SheafOfModules.changeOfRingsHomOfUniverses.{v, u, w, w} α M' m ≫ f) =
      m ≫ extensionHomEquiv α M N f := by
  let t : SheafOfModules.changeOfRingsPresheafOfUniverses.{v, u, w, w} α M' ⟶
      SheafOfModules.changeOfRingsPresheafOfUniverses.{v, u, w, w} α M :=
    { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (m.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{v, u, w, w} α M' m }
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv_naturality_left
      t f
  ext U x
  exact congrArg (fun k : SheafOfModules.changeOfRingsPresheafOfUniverses.{v, u, w, w} α M' ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).obj N.val ↦
      k.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) h

section FirstSheafification
variable {R₀ : Cᵒᵖ ⥤ RingCat.{w}}
  (β : R₀ ⟶ ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (P : PresheafOfModules.{w} R₀)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def sheafifyExtensionHomEquiv :
    (SheafOfModules.changeOfRingsOfUniverses.{v, u, w, w} α
      ((PresheafOfModules.sheafification β).obj P) ⟶ N) ≃
      (P ⟶ (PresheafOfModules.restrictScalars
        (β ≫ ((sheafCompose J (forget₂ CommRingCat RingCat)).map α).hom)).obj N.val) :=
  (extensionHomEquiv α _ N).trans
    (PresheafOfModules.sheafificationHomEquiv β)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem sheafifyExtensionHomEquiv_comp
    {N' : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)}
    (f : SheafOfModules.changeOfRingsOfUniverses.{v, u, w, w} α
      ((PresheafOfModules.sheafification β).obj P) ⟶ N) (g : N ⟶ N') :
    sheafifyExtensionHomEquiv α N' β P (f ≫ g) =
      sheafifyExtensionHomEquiv α N β P f ≫
        (PresheafOfModules.restrictScalars
          (β ≫ ((sheafCompose J (forget₂ CommRingCat RingCat)).map α).hom)).map g.val := by
  exact (congrArg (PresheafOfModules.sheafificationHomEquiv β)
    (extensionHomEquiv_comp α _ N f g)).trans
      ((PresheafOfModules.sheafificationAdjunction β).homEquiv_naturality_right _ _)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem sheafifyExtensionHomEquiv_precomp
    {P' : PresheafOfModules.{w} R₀} (m : P' ⟶ P)
    (f : SheafOfModules.changeOfRingsOfUniverses.{v, u, w, w} α
      ((PresheafOfModules.sheafification β).obj P) ⟶ N) :
    sheafifyExtensionHomEquiv α N β P'
      (SheafOfModules.changeOfRingsHomOfUniverses.{v, u, w, w} α _
        ((PresheafOfModules.sheafification β).map m) ≫ f) =
      m ≫ sheafifyExtensionHomEquiv α N β P f := by
  exact (congrArg (PresheafOfModules.sheafificationHomEquiv β)
    (extensionHomEquiv_precomp α _ N ((PresheafOfModules.sheafification β).map m) f)).trans
      ((PresheafOfModules.sheafificationAdjunction β).homEquiv_naturality_left _ _)
end FirstSheafification

end Extension
section RawSheaf
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A : Type w} [CommRing A] (S : Sheaf J CommRingCat.{w})
  (gamma : (Functor.const Cᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj)
  (M : ModuleCat.{w} A)
  (N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawSheafFunctor : ModuleCat.{w} A ⥤
    SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) :=
  rawFunctor S.obj gamma ⋙ PresheafOfModules.sheafification (𝟙 _)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def rawSheafHomEquiv :
    ((rawSheafFunctor S gamma).obj M ⟶ N) ≃
      (({ obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id } :
        PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of A))) ⟶
        (PresheafOfModules.restrictScalars
          (Functor.whiskerRight gamma (forget₂ CommRingCat RingCat))).obj N.val) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).trans
    (rawHomEquiv S.obj gamma M N.val)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem rawSheafHomEquiv_comp
    {N' : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)}
    (f : (rawSheafFunctor S gamma).obj M ⟶ N) (g : N ⟶ N') :
    rawSheafHomEquiv S gamma M N' (f ≫ g) = rawSheafHomEquiv S gamma M N f ≫
      (PresheafOfModules.restrictScalars
        (Functor.whiskerRight gamma (forget₂ CommRingCat RingCat))).map g.val := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv_naturality_right
      (X := rawObj S.obj gamma M) f g
  ext U x
  exact congrArg (fun k : rawObj S.obj gamma M ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).obj N'.val ↦
      k.app U ((1 : S.obj.obj U) ⊗ₜ[A, (gamma.app U).hom] x)) h

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem rawSheafHomEquiv_precomp {M' : ModuleCat.{w} A} (m : M' ⟶ M)
    (f : (rawSheafFunctor S gamma).obj M ⟶ N) :
    rawSheafHomEquiv S gamma M' N ((rawSheafFunctor S gamma).map m ≫ f) =
      ({ app := fun _ ↦ m } :
        ({ obj := fun _ ↦ M', map := fun _ ↦ ModuleCat.ofHom LinearMap.id } :
          PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of A))) ⟶
        ({ obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id } :
          PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of A)))) ≫
        rawSheafHomEquiv S gamma M N f := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).homEquiv_naturality_left
      ((rawFunctor S.obj gamma).map m) f
  ext U x
  exact congrArg (fun k : rawObj S.obj gamma M' ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).obj N.val ↦
      k.app U ((1 : S.obj.obj U) ⊗ₜ[A, (gamma.app U).hom] x)) h
end RawSheaf



set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def functorComparison {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D)
    (e : ∀ X Y, (F.obj X ⟶ Y) ≃ (G.obj X ⟶ Y))
    (post : ∀ X Y Y' (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
      e X Y' (f ≫ g) = e X Y f ≫ g)
    (pre : ∀ X X' (m : X' ⟶ X) Y (f : F.obj X ⟶ Y),
      e X' Y (F.map m ≫ f) = G.map m ≫ e X Y f) : F ≅ G :=
  NatIso.ofComponents (fun X ↦ (Coyoneda.ext _ _
    (fun {Y} ↦ (e X Y).symm) (fun {Y} ↦ e X Y)
    (fun f ↦ Equiv.apply_symm_apply _ f) (fun f ↦ Equiv.symm_apply_apply _ f)
    (fun _ _ ↦ post X _ _ _ _)).symm) (by
      intro X Y m
      change F.map m ≫ (e Y (G.obj Y)).symm (𝟙 _) =
        (e X (G.obj X)).symm (𝟙 _) ≫ G.map m
      apply (e X (G.obj Y)).injective
      rw [pre, post]
      simp)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def inverseEquivalenceObjIso {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) {M : D} {N : C} (h : M ≅ e.functor.obj N) : e.inverse.obj M ≅ N :=
  e.inverse.mapIso h ≪≫ (e.unitIso.app N).symm


section Point
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
open CategoryTheory.InternalAbelianSheafModule

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def pointScalarComposite :
    (Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)) ⟶
      (sectionRingSheaf (coherentTopology Profinite.{u})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)).obj :=
  toSheafify _ _ ≫ (integralHeartScalarMap.{u} ℓ E).hom

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem pointScalarComposite_eq :
    pointScalarComposite.{u} ℓ E = integralHeartConstantMap.{u} ℓ E := by
  exact ((sheafificationAdjunction (coherentTopology Profinite.{u})
    CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem pointScalar_flat [IsDomain (integralHeartScalars.{u} ℓ E)]
    [IsPrincipalIdealRing (integralHeartScalars.{u} ℓ E)] (U : Profinite.{u}ᵒᵖ) :
    ((pointScalarComposite.{u} ℓ E).app U).hom.Flat := by
  rw [pointScalarComposite_eq]
  let e := continuousSectionEquiv (SmallAdicCompletion.Coefficients.integers ℓ E) U
  apply flat_of_targetIso e
  have he : e.toRingHom.comp ((integralHeartConstantMap.{u} ℓ E).app U).hom =
      continuousConstantMap (SmallAdicCompletion.Coefficients.integers ℓ E) U := by
    ext r
    rfl
  rw [he]
  exact continuousConstantMap_flat _ U

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def pointOrdinary : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
    SheafOfModules.{u + 1} (integralHeartPointRing.{u} ℓ E) :=
  integralHeartConstantPresheaf.{u} ℓ E ⋙
    PresheafOfModules.sheafification
      (R := (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (integralHeartConstantRing.{u} ℓ E)) (integralHeartConstantUnit.{u} ℓ E) ⋙
    integralHeartExtension.{u} ℓ E

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def pointRaw : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
    SheafOfModules.{u + 1} (integralHeartPointRing.{u} ℓ E) :=
  rawFunctor _ (pointScalarComposite.{u} ℓ E) ⋙
    PresheafOfModules.sheafification (𝟙 _)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def pointOrdinaryHomEquiv
    (M : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E))
    (N : SheafOfModules.{u + 1} (integralHeartPointRing.{u} ℓ E)) :
    ((pointOrdinary ℓ E).obj M ⟶ N) ≃
      ((integralHeartConstantPresheaf ℓ E).obj M ⟶
        (PresheafOfModules.restrictScalars
          (Functor.whiskerRight (pointScalarComposite ℓ E)
            (forget₂ CommRingCat RingCat))).obj N.val) :=
  sheafifyExtensionHomEquiv (integralHeartScalarMap ℓ E) N
    (integralHeartConstantUnit ℓ E) ((integralHeartConstantPresheaf ℓ E).obj M)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def pointRawHomEquiv
    (M : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E))
    (N : SheafOfModules.{u + 1} (integralHeartPointRing.{u} ℓ E)) :
    ((pointRaw ℓ E).obj M ⟶ N) ≃
      ((integralHeartConstantPresheaf ℓ E).obj M ⟶
        (PresheafOfModules.restrictScalars
          (Functor.whiskerRight (pointScalarComposite ℓ E)
            (forget₂ CommRingCat RingCat))).obj N.val) :=
  rawSheafHomEquiv _ (pointScalarComposite ℓ E) M N

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def pointComparison : pointOrdinary.{u} ℓ E ≅ pointRaw.{u} ℓ E := by
  apply functorComparison _ _ (fun M N ↦
    (pointOrdinaryHomEquiv ℓ E M N).trans (pointRawHomEquiv ℓ E M N).symm)
  · intro M N N' f g
    apply (pointRawHomEquiv ℓ E M N').injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    have hO := sheafifyExtensionHomEquiv_comp (integralHeartScalarMap ℓ E) N
      (integralHeartConstantUnit ℓ E) ((integralHeartConstantPresheaf ℓ E).obj M) f g
    have hR := rawSheafHomEquiv_comp _ (pointScalarComposite ℓ E) M N
      ((pointRawHomEquiv ℓ E M N).symm (pointOrdinaryHomEquiv ℓ E M N f)) g
    exact hO.trans ((congrArg (fun k ↦ k ≫ _)
      ((pointRawHomEquiv ℓ E M N).apply_symm_apply _)).symm.trans hR.symm)
  · intro M M' m N f
    apply (pointRawHomEquiv ℓ E M' N).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    have hO := sheafifyExtensionHomEquiv_precomp (integralHeartScalarMap ℓ E) N
      (integralHeartConstantUnit ℓ E) ((integralHeartConstantPresheaf ℓ E).obj M)
      ((integralHeartConstantPresheaf ℓ E).map m) f
    have hR := rawSheafHomEquiv_precomp _ (pointScalarComposite ℓ E) M N m
      ((pointRawHomEquiv ℓ E M N).symm (pointOrdinaryHomEquiv ℓ E M N f))
    exact hO.trans ((congrArg (fun k ↦ _ ≫ k)
      ((pointRawHomEquiv ℓ E M N).apply_symm_apply _)).symm.trans hR.symm)

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def pointObjIso (M : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) :=
  (pointComparison.{u} ℓ E).app M

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private def pointRawUnitIso :
    (pointRaw.{u} ℓ E).obj (ModuleCat.of (integralHeartScalars.{u} ℓ E)
      (integralHeartScalars.{u} ℓ E)) ≅
      (sectionModuleEquivalence (coherentTopology Profinite.{u})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)).functor.obj
          (Mod.regular (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)) := by
  let J := coherentTopology Profinite.{u}
  let R := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let T := (sectionModuleFunctor J R).obj (Mod.regular R)
  let H := PresheafOfModules.sheafification (𝟙 (integralHeartPointRing.{u} ℓ E).obj)
  let e : rawObj _ (pointScalarComposite.{u} ℓ E)
      (ModuleCat.of (integralHeartScalars.{u} ℓ E) (integralHeartScalars.{u} ℓ E)) ≅ T.val :=
    rawUnitIso _ _ ≪≫ sectionRegularIso J R
  exact H.mapIso e ≪≫ identitySheafificationIso
    (S := sectionRingSheaf J R) T

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem pointRaw_exact [IsDomain (integralHeartScalars.{u} ℓ E)]
    [IsPrincipalIdealRing (integralHeartScalars.{u} ℓ E)] :
    PreservesFiniteLimits (pointRaw.{u} ℓ E) ∧
      PreservesFiniteColimits (pointRaw.{u} ℓ E) := by
  have := raw_preservesFiniteLimits _ _ (pointScalar_flat.{u} ℓ E)
  have := raw_preservesFiniteColimits
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).obj (pointScalarComposite.{u} ℓ E)
  unfold pointRaw
  exact ⟨inferInstance, inferInstance⟩

set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
private theorem free_dualizable {A : Type w} [CommRing A]
    {D : Type*} [Category D] [Abelian D] [MonoidalCategory D] [MonoidalPreadditive D]
    (F : ModuleCat.{w} A ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (h₁ : IsDualizable (F.obj (ModuleCat.of A A))) (n : ℕ) :
    IsDualizable (F.obj (ModuleCat.of A (Fin n → A))) := by
  let := preservesBinaryBiproducts_of_preservesBiproducts F
  induction n with
  | zero =>
    exact CategoryTheory.IsZero.isDualizable
      (F.map_isZero (ModuleCat.isZero_of_subsingleton _))
  | succ n ih =>
    let e : ModuleCat.of A (Fin (n + 1) → A) ≅
        ModuleCat.of A A ⊞ ModuleCat.of A (Fin n → A) :=
      (Fin.consLinearEquiv A (fun _ : Fin (n + 1) ↦ A)).symm.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd (ModuleCat.of A A) (ModuleCat.of A (Fin n → A))).symm
    exact (h₁.biprod ih).of_iso (F.mapIso e ≪≫ F.mapBiprod _ _).symm


set_option maxHeartbeats 80000 in
-- Bound elaboration search for the explicit scalar-extension comparison.
/-- Completed scalar realization is exact and takes finite free scalar modules to
 dualizable module sheaves.

Source: Stacks Project, Tags 093J and 093M; integral-heart-dualizable, proof steps 1--2.
(blueprint: lem-integral-heart-realization-exact)

Proof: constant module presheaves and module sheafification preserve short exact
sequences. The map from constant scalars to continuous completed coefficients is flat:
its sections are continuous functions into the DVR, hence torsion-free over that PID.
Extension of scalars is
therefore exact. The section-module equivalence and inverse image from the point are
exact, so their composite integralHeartRealization is exact. Constant realization takes
the free scalar module of rank n to the n-fold sum of the constant unit; extension of
scalars takes this sum to the n-fold sum of the completed unit. The equivalence and
strong monoidal inverse image preserve this identification. A finite sum of the unit
is dualizable, including the empty sum when n=0. -/
theorem integralHeartRealization_exact_free (X : Scheme.{u}) :
    PreservesFiniteLimits (integralHeartRealization.{u} ℓ E X) ∧
    PreservesFiniteColimits (integralHeartRealization.{u} ℓ E X) ∧
    ∀ n : ℕ, IsDualizable ((integralHeartRealization.{u} ℓ E X).obj
      (ModuleCat.of (integralHeartScalars.{u} ℓ E)
        (Fin n → integralHeartScalars.{u} ℓ E))) := by
  let O := SmallAdicCompletion.Coefficients.integers ℓ E
  have hDvr : IsDiscreteValuationRing O :=
    (Padic.extension_integers_dvr ℓ (SmallAdicCompletion.Coefficients.field ℓ E)
      (Padic.coefficientExtensionAbsoluteValue ℓ _)
      (spectralNorm_extends (K := Padic ℓ)
        (L := SmallAdicCompletion.Coefficients.field ℓ E))).choose_spec.choose_spec.2.2.2.2.2.2.2.1
  let : IsDiscreteValuationRing O := hDvr
  let : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  let A := integralHeartScalars.{u} ℓ E
  let : IsDomain A := MulEquiv.isDomain O (ULift.ringEquiv (R := O)).toMulEquiv
  let eA := ULift.ringEquiv (R := O)
  let : IsPrincipalIdealRing A :=
    ⟨(isPrincipalIdealRing_iff _).1 (.of_surjective _ eA.symm.surjective)⟩
  obtain ⟨hlim, hcolim⟩ := pointRaw_exact.{u} ℓ E
  let R := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let eqv := sectionModuleEquivalence (coherentTopology Profinite.{u}) R
  let eF : pointRaw.{u} ℓ E ⋙ eqv.inverse ≅ integralHeartPointRealization.{u} ℓ E :=
    (Functor.isoWhiskerRight (pointComparison.{u} ℓ E) eqv.inverse).symm
  have : PreservesFiniteLimits (pointRaw.{u} ℓ E ⋙ eqv.inverse) := inferInstance
  have : PreservesFiniteColimits (pointRaw.{u} ℓ E ⋙ eqv.inverse) := inferInstance
  have : PreservesFiniteLimits (integralHeartPointRealization.{u} ℓ E) :=
    preservesFiniteLimits_of_natIso eF
  have : PreservesFiniteColimits (integralHeartPointRealization.{u} ℓ E) :=
    preservesFiniteColimits_of_natIso eF
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteColimits pointUpperStar.{u} := by
    have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : (upperStarFromPoint X).Additive := leftExactFunctor_le_additiveFunctor _ _ _ (by
    rw [leftExactFunctor_iff]
    infer_instance)
  have : PreservesFiniteLimits (integralHeartRealization.{u} ℓ E X) := by
    unfold integralHeartRealization
    infer_instance
  have : PreservesFiniteColimits (integralHeartRealization.{u} ℓ E X) := by
    unfold integralHeartRealization
    infer_instance
  let e : (integralHeartPointRealization.{u} ℓ E).obj (ModuleCat.of A A) ≅ Mod.regular R :=
    inverseEquivalenceObjIso eqv
      (pointObjIso ℓ E (ModuleCat.of A A) ≪≫ pointRawUnitIso ℓ E)
  let eX : (integralHeartRealization.{u} ℓ E X).obj (ModuleCat.of A A) ≅ 𝟙_ _ :=
    ((upperStarFromPoint X).mapMod R).mapIso e ≪≫
      SmallAdicCompletion.Coefficients.regularPullbackIso ℓ E X
  have h₁ : IsDualizable ((integralHeartRealization.{u} ℓ E X).obj
      (ModuleCat.of A A)) := isDualizable_unit.of_iso eX.symm
  exact ⟨inferInstance, inferInstance,
    free_dualizable (integralHeartRealization.{u} ℓ E X) h₁⟩

end Point
end AlgebraicGeometry.ProEtale
