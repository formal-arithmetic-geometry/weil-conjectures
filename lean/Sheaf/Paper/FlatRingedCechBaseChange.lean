/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.LocalExtendedCechDescription
public import Sheaf.Paper.RingedSiteIdeal
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.Paper.FlatExtendedCechComparison
import Sheaf.Paper.SiteRestrictionExact

/-! # Scalar extension of an augmented Cech model

Source: Stacks Project, Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)

/-- The sectionwise tensor map induced by a module-sheaf morphism.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalarsPresheafMap {M N : SheafOfModules.{u} (siteModuleRings R)} (f : M ⟶ N) :
    SheafOfModules.changeOfRingsPresheaf.{u,u,u} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u,u,u} φ N where
  app U := (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
  naturality := SheafOfModules.changeOfRingsHom_naturality φ M f

/-- The scalar-extension functor with its actual sheafified sectionwise tensors.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalars (φ : R ⟶ B) : SheafOfModules.{u} (siteModuleRings R) ⥤
    SheafOfModules.{u} (siteModuleRings B) where
  obj M := SheafOfModules.changeOfRings.{u,u,u} φ M
  map {M N} f := (PresheafOfModules.sheafification (𝟙 (siteModuleRings B).obj)).map
    (siteExtendScalarsPresheafMap φ f)
  map_id M := by
    change (PresheafOfModules.sheafification (𝟙 (siteModuleRings B).obj)).map
      (siteExtendScalarsPresheafMap φ (𝟙 M)) = _
    have h : siteExtendScalarsPresheafMap φ (𝟙 M) = 𝟙 _ := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_id (M.val.obj U)
    rw [h, Functor.map_id]
    rfl
  map_comp {M N P} f g := by
    change (PresheafOfModules.sheafification (𝟙 (siteModuleRings B).obj)).map
      (siteExtendScalarsPresheafMap φ (f ≫ g)) = _
    have h : siteExtendScalarsPresheafMap φ (f ≫ g) =
        siteExtendScalarsPresheafMap φ f ≫ siteExtendScalarsPresheafMap φ g := by
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_comp (f.val.app U) (g.val.app U)
    rw [h, Functor.map_comp]

/-- Sheafified scalar extension preserves addition of module morphisms.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
instance siteExtendScalars_additive : (siteExtendScalars φ).Additive where
  map_add {M N} f g := by
    let := Functor.additive_of_preserves_binary_products
      (PresheafOfModules.sheafification (𝟙 (siteModuleRings B).obj))
    change (PresheafOfModules.sheafification (𝟙 (siteModuleRings B).obj)).map
      (siteExtendScalarsPresheafMap φ (f + g)) = _
    have h : siteExtendScalarsPresheafMap φ (f + g) =
        siteExtendScalarsPresheafMap φ f + siteExtendScalarsPresheafMap φ g := by
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      let : Module (R.obj.obj U) (B.obj.obj U) :=
        Module.compHom (B.obj.obj U) (φ.hom.app U).hom
      change (1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
        ((f.val.app U + g.val.app U) m) = _
      change (1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
        (f.val.app U m + g.val.app U m) =
          (1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] f.val.app U m +
          (1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] g.val.app U m
      exact TensorProduct.tmul_add _ _ _
    rw [h, Functor.map_add]
    rfl

/-- The sectionwise tensor unit before sheafification.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalarsPresheafUnit (M : SheafOfModules.{u} (siteModuleRings R)) :
    M.val ⟶ (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (SheafOfModules.changeOfRingsPresheaf.{u,u,u} φ M) where
  app U := (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (M.val.obj U)
  naturality {U V} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (1 : B.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] M.val.map g m =
      SheafOfModules.changeOfRingsMap φ M g
        ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
    have h := Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{u,u,u} φ M g) 1 m
    exact (congrArg (fun b : B.obj.obj V ↦
      b ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] M.val.map g m)
        (map_one (B.obj.map g).hom)).symm.trans h.symm

/-- The module-sheafification unit, with the identity scalar restriction reduced.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteScalarSheafificationUnit (P : PresheafOfModules.{u} (siteModuleRings B).obj) :
    P ⟶ ((PresheafOfModules.sheafification (𝟙 (siteModuleRings B).obj)).obj P).val := by
  change P ⟶ (PresheafOfModules.restrictScalars (𝟙 (siteModuleRings B).obj)).obj
    (((PresheafOfModules.sheafification (𝟙 (siteModuleRings B).obj)).obj P).val)
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (siteModuleRings B).obj)).unit.app P

/-- The scalar-extension unit after sheafification.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalarsUnit (M : SheafOfModules.{u} (siteModuleRings R)) :
    M ⟶ (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        ((siteExtendScalars φ).obj M) where
  val := siteExtendScalarsPresheafUnit φ M ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).map
        (siteScalarSheafificationUnit (SheafOfModules.changeOfRingsPresheaf.{u,u,u} φ M))

/-- The tensor-adjoint lift of a map into a restricted module, before sheafification.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalarsPresheafLift {M : SheafOfModules.{u} (siteModuleRings R)}
    {N : SheafOfModules.{u} (siteModuleRings B)}
    (g : M ⟶ (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj N) :
    SheafOfModules.changeOfRingsPresheaf.{u,u,u} φ M ⟶ N.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := R.obj.obj U) («S» := B.obj.obj U) (φ.hom.app U).hom (g.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      («R» := R.obj.obj V) («S» := B.obj.obj V) (φ.hom.app V).hom (g.val.app V)
        (SheafOfModules.changeOfRingsMap φ M i _) =
      N.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        («R» := R.obj.obj U) («S» := B.obj.obj U) (φ.hom.app U).hom (g.val.app U) _)
    rw [show SheafOfModules.changeOfRingsMap φ M i
      ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) =
        B.obj.map i 1 ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] M.val.map i m from
          Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{u,u,u} φ M i) 1 m]
    simp only [map_one]
    let : Module (R.obj.obj V) (B.obj.obj V) :=
      Module.compHom (B.obj.obj V) (φ.hom.app V).hom
    let : Module (R.obj.obj V) (N.val.obj V) :=
      Module.compHom (N.val.obj V) (φ.hom.app V).hom
    let : Module (R.obj.obj U) (B.obj.obj U) :=
      Module.compHom (B.obj.obj U) (φ.hom.app U).hom
    let : Module (R.obj.obj U) (N.val.obj U) :=
      Module.compHom (N.val.obj U) (φ.hom.app U).hom
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := R.obj.obj V) («S» := B.obj.obj V), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := R.obj.obj U) («S» := B.obj.obj U), TensorProduct.lift.tmul]
    change (1 : B.obj.obj V) • (show N.val.obj V from g.val.app V (M.val.map i m)) =
      N.val.map i ((1 : B.obj.obj U) • (show N.val.obj U from g.val.app U m))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply g.val i m

/-- The sheafified tensor-adjoint lift of a map into a restricted module.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalarsLift {M : SheafOfModules.{u} (siteModuleRings R)}
    {N : SheafOfModules.{u} (siteModuleRings B)}
    (g : M ⟶ (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj N) :
    (siteExtendScalars φ).obj M ⟶ N :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (siteModuleRings B).obj)).symm
    (siteExtendScalarsPresheafLift φ g)

/-- Naturality of the scalar-extension unit on sheaves of modules.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
theorem siteExtendScalarsUnit_naturality {M N : SheafOfModules.{u} (siteModuleRings R)}
    (f : M ⟶ N) : f ≫ siteExtendScalarsUnit φ N = siteExtendScalarsUnit φ M ≫
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
          ((siteExtendScalars φ).map f) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have h := ConcreteCategory.congr_hom
    (CategoryTheory.congr_app (CategoryTheory.toSheafify_naturality J
      ((PresheafOfModules.toPresheaf (siteModuleRings B).obj).map
        (siteExtendScalarsPresheafMap φ f))) U)
    ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  exact h

/-- Tensor-adjoint lifting followed by the unit recovers the given linear map.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
theorem siteExtendScalarsLift_unit {M : SheafOfModules.{u} (siteModuleRings R)}
    {N : SheafOfModules.{u} (siteModuleRings B)}
    (g : M ⟶ (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj N) :
    siteExtendScalarsUnit φ M ≫ (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
        (siteExtendScalarsLift φ g) = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  have h := Equiv.apply_symm_apply
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (siteModuleRings B).obj))
      (siteExtendScalarsPresheafLift φ g)
  have he := congrArg (fun k ↦ k.app U) h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hev := ConcreteCategory.congr_hom he
    ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  change (siteExtendScalarsLift φ g).val.app U
    ((siteScalarSheafificationUnit (SheafOfModules.changeOfRingsPresheaf.{u,u,u} φ M)).app U
      ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) = g.val.app U m
  have hev' : (siteExtendScalarsLift φ g).val.app U
      ((siteScalarSheafificationUnit (SheafOfModules.changeOfRingsPresheaf.{u,u,u} φ M)).app U
        ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) =
      (siteExtendScalarsPresheafLift φ g).app U
        ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) := hev
  rw [hev']
  let : Module (R.obj.obj U) (B.obj.obj U) :=
    Module.compHom (B.obj.obj U) (φ.hom.app U).hom
  let : Module (R.obj.obj U) (N.val.obj U) :=
    Module.compHom (N.val.obj U) (φ.hom.app U).hom
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := R.obj.obj U) («S» := B.obj.obj U) (φ.hom.app U).hom (g.val.app U) _ = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
    («R» := R.obj.obj U) («S» := B.obj.obj U), TensorProduct.lift.tmul]
  exact one_smul _ _

/-- The degreewise scalar-extension unit on complexes.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalarsComplexUnit (K : ringedSiteComplex R) :
    K ⟶ ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((siteExtendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) where
  f n := siteExtendScalarsUnit φ (K.X n)
  comm' n m _ := (siteExtendScalarsUnit_naturality φ (K.d n m)).symm

/-- Naturality of the scalar-extension unit on complexes.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
theorem siteExtendScalarsComplexUnit_naturality {K L : ringedSiteComplex R} (f : K ⟶ L) :
    f ≫ siteExtendScalarsComplexUnit φ L = siteExtendScalarsComplexUnit φ K ≫
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            (((siteExtendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact siteExtendScalarsUnit_naturality φ (f.f n)

/-- The lifted coefficient map as a map from the scalar-extended ring complex.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalarsRingCounit
    (a : SheafOfModules.unit (siteModuleRings R) ⟶
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))) :
    ((siteExtendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (ringedSiteRingComplex R) ⟶ ringedSiteRingComplex B :=
  (HomologicalComplex.singleMapHomologicalComplex (siteExtendScalars φ)
    (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit (siteModuleRings R)) ≫
      (HomologicalComplex.single _ _ 0).map (siteExtendScalarsLift φ a)

/-- A linear coefficient map, applied to complexes concentrated in degree zero.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteRingComplexMap
    (a : SheafOfModules.unit (siteModuleRings R) ⟶
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))) :
    ringedSiteRingComplex R ⟶
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (ringedSiteRingComplex B) := by
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  exact (HomologicalComplex.single _ _ 0).map a ≫
    (HomologicalComplex.singleMapHomologicalComplex r (ComplexShape.up ℤ) 0).inv.app _

/-- The lifted coefficient map composed with the unit is the original coefficient map.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
theorem siteExtendScalarsRingCounit_unit
    (a : SheafOfModules.unit (siteModuleRings R) ⟶
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))) :
    siteExtendScalarsComplexUnit φ (ringedSiteRingComplex R) ≫
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (siteExtendScalarsRingCounit φ a) =
      siteRingComplexMap φ a := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    change siteExtendScalarsUnit φ (SheafOfModules.unit (siteModuleRings R)) ≫
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
          (siteExtendScalarsLift φ a) = a
    exact siteExtendScalarsLift_unit φ a
  · let r := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    exact (r.map_isZero (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0 (SheafOfModules.unit (siteModuleRings B)) n hn)).eq_of_tgt _ _

/-- The scalar-extended augmentation followed by multiplication in the target ring.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteExtendScalarsAugmentation
    (a : SheafOfModules.unit (siteModuleRings R) ⟶
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B)))
    {K : ringedSiteComplex R} (ε : K ⟶ ringedSiteRingComplex R) :
    ((siteExtendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      ringedSiteRingComplex B :=
  ((siteExtendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
    siteExtendScalarsRingCounit φ a

/-- The tensor unit commutes with the scalar-extended augmentation.
Source: Stacks Project, Modules on Sites, Tag 03EK; Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
theorem siteExtendScalarsAugmentation_unit
    (a : SheafOfModules.unit (siteModuleRings R) ⟶
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B)))
    {K : ringedSiteComplex R} (ε : K ⟶ ringedSiteRingComplex R) :
    siteExtendScalarsComplexUnit φ K ≫ ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (siteExtendScalarsAugmentation φ a ε) =
      ε ≫ siteRingComplexMap φ a := by
  let r := (SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
      (ComplexShape.up ℤ)
  change siteExtendScalarsComplexUnit φ K ≫ r.map
    (((siteExtendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map ε ≫
      siteExtendScalarsRingCounit φ a) = _
  rw [Functor.map_comp, ← Category.assoc, ← siteExtendScalarsComplexUnit_naturality,
    Category.assoc, siteExtendScalarsRingCounit_unit]

/-- The ring map, viewed as a linear map into the restricted coefficient module.
Source: Stacks Project, Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteRingScalarUnit : SheafOfModules.unit (siteModuleRings R) ⟶
    (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (SheafOfModules.unit (siteModuleRings B)) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (SheafOfModules.unit (siteModuleRings R)).val.obj U)
        (Y := ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
            (SheafOfModules.unit (siteModuleRings B))).val.obj U)
        { toFun := (φ.hom.app U).hom
          map_add' := map_add _
          map_smul' := fun a b ↦ map_mul (φ.hom.app U).hom a b }
      naturality := fun {U V} g ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact ConcreteCategory.congr_hom (φ.hom.naturality g) a }

/-- The same coefficient map on complexes concentrated in degree zero.
Source: Stacks Project, Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change). -/
def siteRingComplexScalarUnit : ringedSiteRingComplex R ⟶
    ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (ringedSiteRingComplex B) :=
  siteRingComplexMap φ (siteRingScalarUnit φ)

/-- Flat base change of an augmented local extended Cech model admits a compatible
quasi-isomorphism. No completeness hypothesis on a derived object is involved.

Source: Stacks Project, algebraization.tex, Tags 099H and 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change).

Proof: form the termwise sheafified tensor product B tensor K, with augmentation induced
by epsilon and multiplication in B. Its scalar-extension unit sends x to 1 tensor x and
commutes with the augmentations by the ring-map identity. Flatness makes scalar extension
exact: tensor the kernel/image short exact sequences defining cohomology. On a generating
slice the local description of K therefore identifies this map with the extended Cech
comparison. Localization commutes with tensor by the mutually inverse maps
b tensor (a/f^n) -> b phi(a)/phi(f)^n and b/phi(f)^n -> b tensor (1/f^n).
Finite products are finite sums. Restriction to a slice is exact and preserves quotients,
and flatness restricts to that slice. The quotient-isomorphism hypothesis thus gives the
quasi-isomorphism on the slice by flat_extendedLocalizationCech_comparison_quasiIso.
Finite type supplies a covering by generating slices; cohomology kernel and cokernel
sheaves vanish on this covering, and hence vanish globally. The zero ideal uses the empty
Cech complex and the unit ideal gives contractible complexes, so both edge cases agree. -/
theorem flat_ringed_cech_base_change_unit_quasiIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (R.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (hK : HasLocalExtendedCechDescription R I.module I.inclusion K ε) :
    QuasiIso (siteExtendScalarsComplexUnit φ K) := by
  sorry

/-- The concrete scalar extension and its unit supply the compatible augmented model.
Source: Stacks Project, Algebraization, Tag 099I.
(blueprint: lem-weil-pbc-flat-ringed-cech-base-change).
Proof: use the degreewise sheafified tensor functor and its augmentation above; the unit
is a quasi-isomorphism by the preceding theorem and commutes with augmentations by
`siteExtendScalarsAugmentation_unit`. -/
theorem flat_ringed_cech_base_change (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (R.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (hK : HasLocalExtendedCechDescription R I.module I.inclusion K ε) :
    ∃ (KB : ringedSiteComplex B) (εB : KB ⟶ ringedSiteRingComplex B)
      (u : K ⟶ ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj KB),
      QuasiIso u ∧ u ≫ ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map εB = ε ≫ siteRingComplexScalarUnit φ := by
  refine ⟨((siteExtendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    siteExtendScalarsAugmentation φ (siteRingScalarUnit φ) ε,
    siteExtendScalarsComplexUnit φ K,
    flat_ringed_cech_base_change_unit_quasiIso φ I hI hflat hquot K ε hK, ?_⟩
  exact siteExtendScalarsAugmentation_unit φ (siteRingScalarUnit φ) ε

end CategoryTheory
