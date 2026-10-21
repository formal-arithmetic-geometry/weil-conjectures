/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Restricted scalar-first K-flat tensor identifications

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 06YT, and
sites-modules.tex, Tags 03EK and 03CY.
(blueprint: lem-pe-restricted-kflat-tensor-identification)

The scalar-last complex is specified by its underlying B-linear tensor complex and
its S-linear swap from the existing scalar-first extension. The pure-tensor equation
fixes the swap, including its inverse, and hence fixes the S-action on the last factor.
No existence choice of an unspecified object or map is used in a definition.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v r wB wA wS wT
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- Ordinary scalar restriction on the given site.
Source: Stacks 03DA (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorScalars {A S : Sheaf J CommRingCat.{r}} (v : A ⟶ S) :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map v)

/-- Scalar restriction preserves finite limits.
Source: Stacks 03DA (blueprint: lem-pe-restricted-kflat-tensor-identification).
Proof: restriction keeps the underlying abelian sheaves; kernels and finite products
are sectionwise. Apply lem-pur-sheaf-ring-coefficient-ordinary-adjunction. -/
@[instance] theorem restrictedTensorScalars_preservesFiniteLimits
    {A S : Sheaf J CommRingCat.{r}} (v : A ⟶ S) :
    PreservesFiniteLimits (restrictedTensorScalars v) := by
  exact (sheafRingCoefficientOrdinaryAdjunction v).choose

/-- Scalar restriction preserves finite colimits.
Source: Stacks 03DA (blueprint: lem-pe-restricted-kflat-tensor-identification).
Proof: cokernels are sheafifications of sectionwise cokernels. Restriction leaves
both underlying abelian presheaves and their sheafifications unchanged. Apply
lem-pur-sheaf-ring-coefficient-ordinary-adjunction. -/
@[instance] theorem restrictedTensorScalars_preservesFiniteColimits
    {A S : Sheaf J CommRingCat.{r}} (v : A ⟶ S) :
    PreservesFiniteColimits (restrictedTensorScalars v) := by
  exact (sheafRingCoefficientOrdinaryAdjunction v).choose_spec.choose

/-- The coefficient sheaf as a module over the source ring.
Source: Stacks 03EK (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorCoefficient
    {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S) :=
  (restrictedTensorScalars φ).obj (unit (derivedChangeRingIndependentCoefficients J S))

/-- The underlying B-linear scalar-last tensor complex, with differential d tensor 1.
Source: Stacks 03EK (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorLastComplex
    {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :=
  ((siteSheafTensorRight (restrictedTensorCoefficient φ)).mapHomologicalComplex (.up ℤ)).obj P

namespace RestrictedTensorProof

variable [HasWeakSheafify J AddCommGrpCat.{r}]

attribute [local irreducible] monoidalCategory cochainModulesMonoidal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option hygiene false in
local notation "𝓡" R => derivedChangeRingIndependentCoefficients J R
set_option hygiene false in
local notation "𝓻" a => (sheafCompose J (forget₂ CommRingCat RingCat)).map a

private noncomputable def restrictSheafifyHom
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj M) ⟶
    (restrictScalars α).obj ((PresheafOfModules.sheafification (𝟙 S.obj)).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app M))

private theorem restrictSheafifyHom_toSheaf
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (toSheaf R).map (restrictSheafifyHom α M) =
      𝟙 ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
  rw [restrictSheafifyHom, PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change (PresheafOfModules.toPresheaf S.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app M) =
    CategoryTheory.toSheafify J M.presheaf
  exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _

attribute [local irreducible] restrictSheafifyHom

private theorem restrictSheafifyHom_isIso
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    IsIso (restrictSheafifyHom α M) := by
  have : IsIso ((toSheaf R).map (restrictSheafifyHom α M)) := by
    rw [restrictSheafifyHom_toSheaf]
    exact IsIso.id _
  exact isIso_of_reflects_iso _ (toSheaf R)

attribute [local instance] restrictSheafifyHom_isIso

private noncomputable def restrictSheafifyIso
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj M) ≅
    (restrictScalars α).obj ((PresheafOfModules.sheafification (𝟙 S.obj)).obj M) :=
  asIso (restrictSheafifyHom α M)

attribute [local irreducible] restrictSheafifyIso

@[simp] private theorem restrictSheafifyIso_hom_toSheaf
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (toSheaf R).map (restrictSheafifyIso α M).hom =
      𝟙 ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
  unfold restrictSheafifyIso
  exact restrictSheafifyHom_toSheaf α M

@[simp] private theorem restrictSheafifyIso_inv_toSheaf
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : PresheafOfModules.{r} S.obj) :
    (toSheaf R).map (restrictSheafifyIso α M).inv =
      𝟙 ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
  have he : (toSheaf R).mapIso (restrictSheafifyIso α M) =
      Iso.refl ((PresheafOfModules.toPresheaf S.obj ⋙
        presheafToSheaf J AddCommGrpCat).obj M) := by
    apply Iso.ext
    exact restrictSheafifyIso_hom_toSheaf α M
  exact congrArg Iso.inv he

private noncomputable def swapApp {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf φ M)).obj U ≅
    (siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val).obj U := by
  let e : (((PresheafOfModules.restrictScalars (𝓻 φ).hom).obj
      (changeOfRingsPresheaf φ M)).obj U) ≃ₗ[B.obj.obj U]
      TensorProduct (B.obj.obj U) ((restrictedTensorCoefficient φ).val.obj U) (M.val.obj U) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro b x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul s m => rfl
        | add x y hx hy => simpa only [smul_add] using congrArg₂ (· + ·) hx hy }
  exact (e.trans (TensorProduct.comm _ _ _)).toModuleIso

private theorem swapApp_tmul {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (swapApp φ M U).hom (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m) =
      m ⊗ₜ[B.obj.obj U] (show (restrictedTensorCoefficient φ).val.obj U from s) := rfl

attribute [local irreducible] swapApp

private noncomputable def swapPresheafIso {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) :
    (PresheafOfModules.restrictScalars (𝓻 φ).hom).obj (changeOfRingsPresheaf φ M) ≅
      siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val :=
  PresheafOfModules.isoMk (swapApp φ M) (by
    intro U V i
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change (swapApp φ M V).hom (changeOfRingsMap φ M i
        (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)) = _
      erw [Classical.choose_spec (exists_changeOfRingsMap φ M i) s m]
      rw [swapApp_tmul]
      change _ = (siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val).map i
        ((swapApp φ M U).hom (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m))
      rw [swapApp_tmul]
      rfl)

private theorem swapPresheafIso_tmul {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (swapPresheafIso φ M).hom.app U (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m) =
      m ⊗ₜ[B.obj.obj U] (show (restrictedTensorCoefficient φ).val.obj U from s) :=
  swapApp_tmul φ M U s m

attribute [local irreducible] swapPresheafIso

private noncomputable def swapSheafIso {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) :
    (restrictedTensorScalars φ).obj (changeOfRings φ M) ≅
      (siteSheafTensorRight (restrictedTensorCoefficient φ)).obj M :=
  (restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf φ M)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)).mapIso (swapPresheafIso φ M)

private noncomputable def changeMap {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    {M N : SheafOfModules.{r} (𝓡 B)} (a : M ⟶ N) :
    changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N where
  app U := (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U)
  naturality := changeOfRingsHom_naturality φ M a

private theorem changeMap_toSheaf
    {B A S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S) (v : A ⟶ S)
    {M N : SheafOfModules.{r} (𝓡 B)} (a : M ⟶ N) :
    (toSheaf (𝓡 A)).map ((restrictedTensorScalars v).map (changeOfRingsHom φ M a)) =
      (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf (𝓡 A).obj).map
          ((PresheafOfModules.restrictScalars (𝓻 v).hom).map (changeMap φ a))) := rfl

private theorem swapSheafIso_toSheaf {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) :
    (toSheaf (𝓡 B)).map (swapSheafIso φ M).hom =
      (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf (𝓡 B).obj).map (swapPresheafIso φ M).hom) := by
  change (toSheaf (𝓡 B)).map
      ((restrictSheafifyIso (𝓻 φ) (changeOfRingsPresheaf φ M)).inv ≫
        (PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)).map
          (swapPresheafIso φ M).hom) = _
  rw [Functor.map_comp, restrictSheafifyIso_inv_toSheaf]
  erw [Category.id_comp]
  rfl

attribute [local irreducible] swapSheafIso

private theorem swapSheafIso_naturality {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    {M N : SheafOfModules.{r} (𝓡 B)} (a : M ⟶ N) :
    (restrictedTensorScalars φ).map (changeOfRingsHom φ M a) ≫
      (swapSheafIso φ N).hom =
    (swapSheafIso φ M).hom ≫ (siteSheafTensorRight (restrictedTensorCoefficient φ)).map a := by
  have hp : (PresheafOfModules.restrictScalars (𝓻 φ).hom).map (changeMap φ a) ≫
      (swapPresheafIso φ N).hom =
    (swapPresheafIso φ M).hom ≫ siteTensorHom a.val (restrictedTensorCoefficient φ).val := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change (swapPresheafIso φ N).hom.app U
          (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] a.val.app U m) =
        (siteTensorHom a.val (restrictedTensorCoefficient φ).val).app U
          ((swapPresheafIso φ M).hom.app U
            (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m))
      rw [swapPresheafIso_tmul, swapPresheafIso_tmul]
      rfl
  apply (toSheaf (𝓡 B)).map_injective
  simp only [Functor.map_comp, swapSheafIso_toSheaf]
  change (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf (𝓡 B).obj).map
        ((PresheafOfModules.restrictScalars (𝓻 φ).hom).map (changeMap φ a))) ≫ _ =
    _ ≫ (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf (𝓡 B).obj).map
        (siteTensorHom a.val (restrictedTensorCoefficient φ).val))
  simp only [← Functor.map_comp]
  rw [hp]

private theorem swapSheafIso_tmul {B S : Sheaf J CommRingCat.{r}} (φ : B ⟶ S)
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (swapSheafIso φ M).hom.val.app U
      ((CategoryTheory.toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)) =
      siteSheafTensorTmul M (restrictedTensorCoefficient φ) U m s := by
  have hn := CategoryTheory.toSheafify_naturality J
    ((PresheafOfModules.toPresheaf (𝓡 B).obj).map (swapPresheafIso φ M).hom)
  change ((toSheaf (𝓡 B)).map (swapSheafIso φ M).hom).hom.app U _ = _
  rw [swapSheafIso_toSheaf]
  have ht := (CategoryTheory.congr_fun (NatTrans.congr_app hn U)
    (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)).symm
  change _ = (CategoryTheory.toSheafify J
    (siteTensorPresheaf M.val (restrictedTensorCoefficient φ).val).presheaf).app U
      ((swapPresheafIso φ M).hom.app U
        (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] m)) at ht
  rw [swapPresheafIso_tmul] at ht
  exact ht

private noncomputable def coefficientApp
    {B A S T : Sheaf J CommRingCat.{r}} (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (h : (restrictedTensorScalars v).obj (unit (𝓡 S)) ⟶
      (restrictedTensorScalars w).obj (unit (𝓡 T)))
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (𝓻 v).hom).obj
      (changeOfRingsPresheaf (u ≫ v) M)).obj U ⟶
    ((PresheafOfModules.restrictScalars (𝓻 w).hom).obj
      (changeOfRingsPresheaf (u ≫ w) M)).obj U := by
  let hB : (restrictedTensorCoefficient (u ≫ v)).val.obj U →ₗ[B.obj.obj U]
      (restrictedTensorCoefficient (u ≫ w)).val.obj U :=
    { toFun := h.val.app U
      map_add' := map_add _
      map_smul' := fun b s ↦ (h.val.app U).hom.map_smul (u.hom.app U b) s }
  refine ModuleCat.ofHom
    (X := ((PresheafOfModules.restrictScalars (𝓻 v).hom).obj
      (changeOfRingsPresheaf (u ≫ v) M)).obj U)
    (Y := ((PresheafOfModules.restrictScalars (𝓻 w).hom).obj
      (changeOfRingsPresheaf (u ≫ w) M)).obj U)
    { toFun := TensorProduct.map hB (LinearMap.id : M.val.obj U →ₗ[B.obj.obj U] M.val.obj U)
      map_add' := map_add _
      map_smul' := ?_ }
  intro a x
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul s m =>
    change (show T.obj.obj U from h.val.app U
        ((v.hom.app U a) * (show S.obj.obj U from s))) ⊗ₜ[B.obj.obj U,
        ((u ≫ w).hom.app U).hom] m =
      ((w.hom.app U a) * (show T.obj.obj U from h.val.app U s)) ⊗ₜ[B.obj.obj U,
        ((u ≫ w).hom.app U).hom] m
    exact congrArg (fun t : T.obj.obj U ↦
      t ⊗ₜ[B.obj.obj U, ((u ≫ w).hom.app U).hom] m)
        ((h.val.app U).hom.map_smul a s)

private theorem coefficientApp_tmul
    {B A S T : Sheaf J CommRingCat.{r}} (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (h : (restrictedTensorScalars v).obj (unit (𝓡 S)) ⟶
      (restrictedTensorScalars w).obj (unit (𝓡 T)))
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    coefficientApp u v w h M U (s ⊗ₜ[B.obj.obj U, ((u ≫ v).hom.app U).hom] m) =
      (show T.obj.obj U from h.val.app U s) ⊗ₜ[B.obj.obj U,
        ((u ≫ w).hom.app U).hom] m := rfl

attribute [local irreducible] coefficientApp

private noncomputable def coefficientPresheafMap
    {B A S T : Sheaf J CommRingCat.{r}} (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (h : (restrictedTensorScalars v).obj (unit (𝓡 S)) ⟶
      (restrictedTensorScalars w).obj (unit (𝓡 T))) (M : SheafOfModules.{r} (𝓡 B)) :
    (PresheafOfModules.restrictScalars (𝓻 v).hom).obj
      (changeOfRingsPresheaf (u ≫ v) M) ⟶
    (PresheafOfModules.restrictScalars (𝓻 w).hom).obj
      (changeOfRingsPresheaf (u ≫ w) M) where
  app U := coefficientApp u v w h M U
  naturality {U V} i := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change coefficientApp u v w h M V
          (changeOfRingsMap (u ≫ v) M i
            (s ⊗ₜ[B.obj.obj U, ((u ≫ v).hom.app U).hom] m)) =
        changeOfRingsMap (u ≫ w) M i
          (coefficientApp u v w h M U
            (s ⊗ₜ[B.obj.obj U, ((u ≫ v).hom.app U).hom] m))
      rw [coefficientApp_tmul]
      erw [Classical.choose_spec (exists_changeOfRingsMap (u ≫ v) M i) s m,
        Classical.choose_spec (exists_changeOfRingsMap (u ≫ w) M i) (h.val.app U s) m]
      rw [coefficientApp_tmul]
      exact congrArg (fun t : T.obj.obj V ↦
        t ⊗ₜ[B.obj.obj V, ((u ≫ w).hom.app V).hom] M.val.map i m)
          (PresheafOfModules.naturality_apply h.val i s)

private noncomputable def coefficientSheafMap
    {B A S T : Sheaf J CommRingCat.{r}} (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (h : (restrictedTensorScalars v).obj (unit (𝓡 S)) ⟶
      (restrictedTensorScalars w).obj (unit (𝓡 T))) (M : SheafOfModules.{r} (𝓡 B)) :
    (restrictedTensorScalars v).obj (changeOfRings (u ≫ v) M) ⟶
    (restrictedTensorScalars w).obj (changeOfRings (u ≫ w) M) :=
  (restrictSheafifyIso (𝓻 v) (changeOfRingsPresheaf (u ≫ v) M)).inv ≫
    (PresheafOfModules.sheafification (𝟙 (𝓡 A).obj)).map
      (coefficientPresheafMap u v w h M) ≫
    (restrictSheafifyIso (𝓻 w) (changeOfRingsPresheaf (u ≫ w) M)).hom

private theorem coefficientSheafMap_toSheaf
    {B A S T : Sheaf J CommRingCat.{r}} (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (h : (restrictedTensorScalars v).obj (unit (𝓡 S)) ⟶
      (restrictedTensorScalars w).obj (unit (𝓡 T))) (M : SheafOfModules.{r} (𝓡 B)) :
    (toSheaf (𝓡 A)).map (coefficientSheafMap u v w h M) =
      (presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf (𝓡 A).obj).map
          (coefficientPresheafMap u v w h M)) := by
  simp only [coefficientSheafMap, Functor.map_comp,
    restrictSheafifyIso_hom_toSheaf, restrictSheafifyIso_inv_toSheaf]
  rfl

attribute [local irreducible] coefficientSheafMap

private theorem coefficientSheafMap_naturality
    {B A S T : Sheaf J CommRingCat.{r}} (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (h : (restrictedTensorScalars v).obj (unit (𝓡 S)) ⟶
      (restrictedTensorScalars w).obj (unit (𝓡 T)))
    {M N : SheafOfModules.{r} (𝓡 B)} (a : M ⟶ N) :
    (restrictedTensorScalars v).map (changeOfRingsHom (u ≫ v) M a) ≫
      coefficientSheafMap u v w h N =
    coefficientSheafMap u v w h M ≫
      (restrictedTensorScalars w).map (changeOfRingsHom (u ≫ w) M a) := by
  have hp : (PresheafOfModules.restrictScalars (𝓻 v).hom).map (changeMap (u ≫ v) a) ≫
      coefficientPresheafMap u v w h N =
    coefficientPresheafMap u v w h M ≫
      (PresheafOfModules.restrictScalars (𝓻 w).hom).map (changeMap (u ≫ w) a) := by
    ext U x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change coefficientApp u v w h N U
          ((ModuleCat.extendScalars ((u ≫ v).hom.app U).hom).map (a.val.app U)
            (s ⊗ₜ[B.obj.obj U, ((u ≫ v).hom.app U).hom] m)) =
        (ModuleCat.extendScalars ((u ≫ w).hom.app U).hom).map (a.val.app U)
          (coefficientApp u v w h M U
            (s ⊗ₜ[B.obj.obj U, ((u ≫ v).hom.app U).hom] m))
      rw [ModuleCat.ExtendScalars.map_tmul, coefficientApp_tmul,
        coefficientApp_tmul, ModuleCat.ExtendScalars.map_tmul]
  apply (toSheaf (𝓡 A)).map_injective
  simp only [Functor.map_comp, coefficientSheafMap_toSheaf]
  rw [changeMap_toSheaf, changeMap_toSheaf]
  simp only [← Functor.map_comp]
  rw [hp]

private theorem coefficientSheafMap_tmul
    {B A S T : Sheaf J CommRingCat.{r}} (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (h : (restrictedTensorScalars v).obj (unit (𝓡 S)) ⟶
      (restrictedTensorScalars w).obj (unit (𝓡 T)))
    (M : SheafOfModules.{r} (𝓡 B)) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (coefficientSheafMap u v w h M).val.app U
      ((CategoryTheory.toSheafify J (changeOfRingsPresheaf (u ≫ v) M).presheaf).app U
        (s ⊗ₜ[B.obj.obj U, ((u ≫ v).hom.app U).hom] m)) =
      (CategoryTheory.toSheafify J (changeOfRingsPresheaf (u ≫ w) M).presheaf).app U
        (h.val.app U s ⊗ₜ[B.obj.obj U, ((u ≫ w).hom.app U).hom] m) := by
  have hn := CategoryTheory.toSheafify_naturality J
    ((PresheafOfModules.toPresheaf (𝓡 A).obj).map (coefficientPresheafMap u v w h M))
  change ((toSheaf (𝓡 A)).map (coefficientSheafMap u v w h M)).hom.app U _ = _
  rw [coefficientSheafMap_toSheaf]
  have ht := (CategoryTheory.congr_fun (NatTrans.congr_app hn U)
    (s ⊗ₜ[B.obj.obj U, ((u ≫ v).hom.app U).hom] m)).symm
  change _ = (CategoryTheory.toSheafify J
    (changeOfRingsPresheaf (u ≫ w) M).presheaf).app U
      (coefficientApp u v w h M U
        (s ⊗ₜ[B.obj.obj U, ((u ≫ v).hom.app U).hom] m)) at ht
  rw [coefficientApp_tmul] at ht
  exact ht

end RestrictedTensorProof

variable {B A S T : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wA} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J A))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

/-- A pure scalar-first section in the prescribed ordinary extension functor.
Source: Stacks 03EK (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable def restrictedTensorFirstSection {φ : B ⟶ S}
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U) :
    (D.E.obj (P.X n)).val.obj U :=
  (eqToHom (D.obj_eq (P.X n)).symm).val.app U
    ((CategoryTheory.toSheafify J (changeOfRingsPresheaf φ (P.X n)).presheaf).app U
      (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] p))

/-- The canonical localization comparison for restriction (oriented as lambda in the node).
Source: Stacks 05RU (blueprint: lem-pe-restricted-kflat-tensor-identification). -/
noncomputable abbrev restrictedTensorLocalization (v : A ⟶ S) :=
  (restrictedTensorScalars v).mapDerivedCategoryFactors.symm

/-- Termwise restriction preserves quasi-isomorphisms, without a flatness hypothesis.
Source: Stacks 03DA, 05RU (blueprint: lem-pe-restricted-kflat-tensor-identification).
Proof: exact restriction identifies the cohomology of the restricted complex with
restriction of its cohomology. Thus an isomorphism on each cohomology stays one. -/
theorem restrictedTensorScalars_quasiIso (v : A ⟶ S)
    {H H' : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) ℤ}
    (a : H ⟶ H') [QuasiIso a] :
    QuasiIso (((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).map a) := by
  infer_instance

/-- The natural localization comparison is compatible with shifts.
Source: Stacks 05RU (blueprint: lem-pe-restricted-kflat-tensor-identification).
Proof: restriction leaves differentials and additive maps unchanged, hence commutes
with degree-one shift and negation of the differential. Localization transports
this identity. The two comparisons agree after Q, so uniqueness gives compatibility. -/
theorem restrictedTensorLocalization_commShift (v : A ⟶ S) :
    NatTrans.CommShift (restrictedTensorLocalization v).hom ℤ := by
  infer_instance

open RestrictedTensorProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ordinarySwapIso {φ : B ⟶ S}
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} φ) :
    D.E ⋙ restrictedTensorScalars φ ≅ siteSheafTensorRight (restrictedTensorCoefficient φ) :=
  NatIso.ofComponents (fun M ↦
    (restrictedTensorScalars φ).mapIso (eqToIso (D.obj_eq M)) ≪≫ swapSheafIso φ M) (by
      intro M N a
      dsimp
      rw [D.map_eq]
      simp only [Functor.map_comp, Category.assoc, eqToHom_map,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [swapSheafIso_naturality φ a])

/-- The scalar-last S-linear model and its normalized K-flat and derived comparisons.
Source: Stacks 03EK, 06YT, 06YY (blueprint: lem-pe-restricted-kflat-tensor-identification).
The underlying B-linear model is the actual sheafified tensor P tensor S. The swap
normalization specifies s tensor p mapping to p tensor s, so S acts on the last factor.
The counit normalization specifies the canonical computation comparison for f.
Eta and delta are included with equations fixing exactly the composites in the node. -/
structure RestrictedKFlatTensorIdentification (u : B ⟶ A) (v : A ⟶ S)
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (u ≫ v))
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (P G : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G) [QuasiIso f] where
  /-- The S-linear scalar-last complex. -/
  H : CochainComplex (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S)) ℤ
  /-- The S-linear cochain swap, including its inverse. -/
  τ : (D.E.mapHomologicalComplex (.up ℤ)).obj P ≅ H
  /-- Identification with the existing B-linear scalar-last tensor complex. -/
  last : ((restrictedTensorScalars (u ≫ v)).mapHomologicalComplex (.up ℤ)).obj H ≅
    restrictedTensorLastComplex (u ≫ v) P
  /-- The swap is the specified pure-tensor exchange. -/
  swap : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U),
    (last.hom.f n).val.app U ((τ.hom.f n).val.app U
      (restrictedTensorFirstSection D P n U s p)) =
      siteSheafTensorTmul (P.X n) (restrictedTensorCoefficient (u ≫ v)) U p s
  /-- The K-flat computation comparison. -/
  c : D.T.obj (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj H
  /-- The computation is the inverse resolution map followed by the K-flat counit. -/
  computation : c.hom ≫ DerivedCategory.Q.map τ.inv =
    inv (D.T.map (DerivedCategory.Q.map f)) ≫ D.ε.app P
  /-- The comparison for the represented derived object K. -/
  η : D.T.obj K ≅ DerivedCategory.Q.obj H
  /-- Eta is exactly c composed with F(e inverse). -/
  eta_eq : η = D.T.mapIso e.symm ≪≫ c
  /-- The restricted scalar-first derived identification. -/
  δ : DerivedCategory.Q.obj
      (((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).obj
        ((D.E.mapHomologicalComplex (.up ℤ)).obj P)) ≅
    (restrictedTensorScalars v).mapDerivedCategory.obj (D.T.obj K)
  /-- Delta is the composite displayed in the node, in its stated order. -/
  delta_eq : δ = DerivedCategory.Q.mapIso
      (((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).mapIso τ) ≪≫
    (restrictedTensorLocalization v).app H ≪≫
    (restrictedTensorScalars v).mapDerivedCategory.mapIso η.symm

/-- Restricted scalar-first K-flat models identify derived scalar extensions.
Source: Stacks 06YY, 06YT, 03EK, 03CY.
(blueprint: lem-pe-restricted-kflat-tensor-identification)

Proof: exact scalar restriction preserves cohomology, hence quasi-isomorphisms
(lem-pur-sheaf-ring-coefficient-ordinary-adjunction). Its localization comparison
is natural and shift compatible by the universal property of Q. Construct the
scalar-last model by sheafifying the sectionwise tensor with S in the second
factor, with S acting there. The mutually inverse pure-tensor swaps are balanced,
commute with restrictions and differentials, and are S-linear. Sheafification
extends them uniquely (def-pur-sheaf-tensor-product and
 def-weil-presheaf-modules-sheafification). Thus no degree sign occurs. The canonical
K-flat counit of lem-pur-derived-change-of-rings and the inverse of F(Q f) give c.
Compose with F(e inverse) to obtain eta. Localize and restrict the swap, follow it
by lambda, and then by restriction of eta inverse to obtain delta. Each factor is
an isomorphism, so the reverse composite of their inverses is its inverse.
Neither flatness of the ring maps nor boundedness or completeness is used. -/
theorem nonempty_restrictedKFlatTensorIdentification (u : B ⟶ A) (v : A ⟶ S)
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (u ≫ v))
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (P G : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G) [QuasiIso f]
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P)
    (hflat : ∀ n : ℤ, IsFlatOnSite (R := B) (P.X n)) :
    Nonempty (RestrictedKFlatTensorIdentification u v D K P G e f) := by
  classical
  have := hflat
  let H := (D.E.mapHomologicalComplex (.up ℤ)).obj P
  let last : ((restrictedTensorScalars (u ≫ v)).mapHomologicalComplex (.up ℤ)).obj H ≅
      restrictedTensorLastComplex (u ≫ v) P :=
    (NatIso.mapHomologicalComplex (ordinarySwapIso D) (.up ℤ)).app P
  have := D.computes P hP
  let c : D.T.obj (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj H :=
    (D.T.mapIso (asIso (DerivedCategory.Q.map f))).symm ≪≫ asIso (D.ε.app P)
  let η := D.T.mapIso e.symm ≪≫ c
  refine ⟨{ H := H
            τ := Iso.refl _
            last := last
            swap := ?_
            c := c
            computation := ?_
            η := η
            eta_eq := rfl
            δ := (restrictedTensorLocalization v).app H ≪≫
              (restrictedTensorScalars v).mapDerivedCategory.mapIso η.symm
            delta_eq := ?_ }⟩
  · intro n U s p
    change ((restrictedTensorScalars (u ≫ v)).map (eqToHom (D.obj_eq (P.X n))) ≫
      (swapSheafIso (u ≫ v) (P.X n)).hom).val.app U
        (restrictedTensorFirstSection D P n U s p) = _
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      restrictedTensorFirstSection]
    change (swapSheafIso (u ≫ v) (P.X n)).hom.val.app U
      (((eqToHom (D.obj_eq (P.X n)).symm ≫ eqToHom (D.obj_eq (P.X n))).val.app U)
        _) = _
    simp only [eqToHom_trans, eqToHom_refl, id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply]
    exact swapSheafIso_tmul (u ≫ v) (P.X n) U s p
  · simp [c, H]
  · simp

variable [HasDerivedCategory.{wT} (ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J T))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def ordinaryCoefficientMap
    (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (DS : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (u ≫ v))
    (DT : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wT} (u ≫ w))
    (h : (restrictedTensorScalars v).obj (unit (derivedChangeRingIndependentCoefficients J S)) ⟶
      (restrictedTensorScalars w).obj (unit (derivedChangeRingIndependentCoefficients J T))) :
    DS.E ⋙ restrictedTensorScalars v ⟶ DT.E ⋙ restrictedTensorScalars w where
  app M := (restrictedTensorScalars v).map (eqToHom (DS.obj_eq M)) ≫
    coefficientSheafMap u v w h M ≫
    (restrictedTensorScalars w).map (eqToHom (DT.obj_eq M).symm)
  naturality M N a := by
    dsimp
    rw [DS.map_eq, DT.map_eq]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (coefficientSheafMap_naturality u v w h a)]

/-- An arbitrary A-linear coefficient map commutes with the scalar swap, and the
localized map is exactly the map on scalar-last representatives under delta.
Source: Stacks 03EK, 03CY, 06YY.
(blueprint: lem-pe-restricted-kflat-tensor-identification)

Proof: A-linearity of h implies B-linearity through u. The formulas h tensor 1
and 1 tensor h therefore respect B-balancing. They respect the A-actions since h
is A-linear, commute with restrictions by naturality of h, and commute with the
differentials because h is in degree zero. Sheafification extends them uniquely.
Both routes around the swap square send s tensor p to p tensor h(s); equality on
pure tensors, followed by uniqueness of sheafification, gives the cochain square.
Localize that square and substitute delta's three factors. The adjacent swap and
inverse swap cancel. The remaining factors are exactly the displayed conjugation
through lambda and eta. This does not apply naturality of lambda to a map between
different coefficient categories and needs neither multiplicativity nor unitality
of h. This is steps 6 and 7 of the node's proof, using the tensor and sheafification
nodes together with def-pc-sheaf-restrict-scalars. -/
theorem restrictedKFlatTensorIdentification_coefficientMap
    (u : B ⟶ A) (v : A ⟶ S) (w : A ⟶ T)
    (DS : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (u ≫ v))
    (DT : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wT} (u ≫ w))
    (K : DerivedCategory (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)))
    (P G : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ)
    (e : DerivedCategory.Q.obj G ≅ K) (f : P ⟶ G) [QuasiIso f]
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P)
    (hflat : ∀ n : ℤ, IsFlatOnSite (R := B) (P.X n))
    (dS : RestrictedKFlatTensorIdentification u v DS K P G e f)
    (dT : RestrictedKFlatTensorIdentification u w DT K P G e f)
    (h : (restrictedTensorScalars v).obj (unit (derivedChangeRingIndependentCoefficients J S)) ⟶
      (restrictedTensorScalars w).obj (unit (derivedChangeRingIndependentCoefficients J T))) :
    ∃ (a : ((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).obj
          ((DS.E.mapHomologicalComplex (.up ℤ)).obj P) ⟶
        ((restrictedTensorScalars w).mapHomologicalComplex (.up ℤ)).obj
          ((DT.E.mapHomologicalComplex (.up ℤ)).obj P))
      (b : ((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).obj dS.H ⟶
        ((restrictedTensorScalars w).mapHomologicalComplex (.up ℤ)).obj dT.H),
      (∀ (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U),
        (a.f n).val.app U (restrictedTensorFirstSection DS P n U s p) =
          restrictedTensorFirstSection DT P n U (h.val.app U s) p) ∧
      (∀ (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U),
        (dT.last.hom.f n).val.app U ((b.f n).val.app U ((dS.τ.hom.f n).val.app U
          (restrictedTensorFirstSection DS P n U s p))) =
          siteSheafTensorTmul (P.X n) (restrictedTensorCoefficient (u ≫ w)) U p
            (h.val.app U s)) ∧
      a ≫ ((restrictedTensorScalars w).mapHomologicalComplex (.up ℤ)).map dT.τ.hom =
        ((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).map dS.τ.hom ≫ b ∧
      dS.δ.inv ≫ DerivedCategory.Q.map a ≫ dT.δ.hom =
        (restrictedTensorScalars v).mapDerivedCategory.map dS.η.hom ≫
          (restrictedTensorLocalization v).inv.app dS.H ≫ DerivedCategory.Q.map b ≫
          (restrictedTensorLocalization w).hom.app dT.H ≫
          (restrictedTensorScalars w).mapDerivedCategory.map dT.η.inv := by
  classical
  have := hP
  have := hflat
  let a : ((restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)).obj
      ((DS.E.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((restrictedTensorScalars w).mapHomologicalComplex (.up ℤ)).obj
        ((DT.E.mapHomologicalComplex (.up ℤ)).obj P) :=
    (NatTrans.mapHomologicalComplex (ordinaryCoefficientMap u v w DS DT h) (.up ℤ)).app P
  let Rv := (restrictedTensorScalars v).mapHomologicalComplex (.up ℤ)
  let Rw := (restrictedTensorScalars w).mapHomologicalComplex (.up ℤ)
  let b := Rv.map dS.τ.inv ≫ a ≫ Rw.map dT.τ.hom
  have ha : ∀ (n : ℤ) (U : Cᵒᵖ) (s : S.obj.obj U) (p : (P.X n).val.obj U),
      (a.f n).val.app U (restrictedTensorFirstSection DS P n U s p) =
        restrictedTensorFirstSection DT P n U (h.val.app U s) p := by
    intro n U s p
    change (((restrictedTensorScalars v).map (eqToHom (DS.obj_eq (P.X n))) ≫
      coefficientSheafMap u v w h (P.X n) ≫
      (restrictedTensorScalars w).map (eqToHom (DT.obj_eq (P.X n)).symm)).val.app U)
        (restrictedTensorFirstSection DS P n U s p) = _
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      restrictedTensorFirstSection]
    change (eqToHom (DT.obj_eq (P.X n)).symm).val.app U
      ((coefficientSheafMap u v w h (P.X n)).val.app U
        (((eqToHom (DS.obj_eq (P.X n)).symm ≫
          eqToHom (DS.obj_eq (P.X n))).val.app U) _)) = _
    simp only [eqToHom_trans, eqToHom_refl, id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply]
    rw [coefficientSheafMap_tmul]
  have hb : Rv.map dS.τ.hom ≫ b = a ≫ Rw.map dT.τ.hom := by
    simp [b, ← Functor.map_comp_assoc]
  refine ⟨a, b, ha, ?_, hb.symm, ?_⟩
  · intro n U s p
    change (dT.last.hom.f n).val.app U
      (((Rv.map dS.τ.hom ≫ b).f n).val.app U
        (restrictedTensorFirstSection DS P n U s p)) = _
    rw [hb]
    change (dT.last.hom.f n).val.app U ((dT.τ.hom.f n).val.app U
      ((a.f n).val.app U (restrictedTensorFirstSection DS P n U s p))) = _
    rw [ha]
    exact dT.swap n U (h.val.app U s) p
  · have hq : DerivedCategory.Q.map a ≫ DerivedCategory.Q.map (Rw.map dT.τ.hom) =
        DerivedCategory.Q.map (Rv.map dS.τ.hom) ≫ DerivedCategory.Q.map b := by
      rw [← Functor.map_comp, ← hb, Functor.map_comp]
    rw [dS.delta_eq, dT.delta_eq]
    simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
    rw [reassoc_of% hq]
    dsimp only [Rv]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]

end SheafOfModules
