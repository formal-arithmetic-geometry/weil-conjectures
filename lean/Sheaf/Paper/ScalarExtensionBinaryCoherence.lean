/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions
import Mathlib.Tactic.CategoryTheory.Slice
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-!
# Binary scalar-extension comparisons

Source: Stacks Project, Tag 03EK.
(blueprint: lem-sp-scalar-extension-binary-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u m

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

set_option hygiene false in
local notation:max "Mod" R:arg =>
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
set_option hygiene false in
local notation:max "𝒪" R:arg => unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
set_option hygiene false in
local notation:max "𝒯" N:arg P:arg => (siteSheafTensorRight P).obj N

/-- Sectionwise multiplication identifies scalar extension of the unit with the target unit.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarExtensionUnitRawIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    changeOfRingsPresheafOfUniverses α (𝒪 R) ≅ (𝒪 S).val :=
  PresheafOfModules.isoMk (fun U ↦ by
    let := (α.hom.app U).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid
      (R.obj.obj U) (S.obj.obj U) (S.obj.obj U)).toModuleIso) (by
    intro U V i
    let := (α.hom.app U).hom.toAlgebra
    let := (α.hom.app V).hom.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro a
    change (TensorProduct.AlgebraTensorModule.rid
        (R.obj.obj V) (S.obj.obj V) (S.obj.obj V))
        (changeOfRingsMapOfUniverses α (𝒪 R) i
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] a)) = _
    rw [changeOfRingsMap_tmulOfUniverses]
    change (α.hom.app V (R.obj.map i a)) * S.obj.map i 1 =
      S.obj.map i ((α.hom.app U a) * 1)
    simp only [map_one, mul_one]
    exact ConcreteCategory.congr_hom (α.hom.naturality i) a)

/-- Sheafify the explicit multiplication isomorphism and compose with the counit.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarExtensionUnitIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) :
    changeOfRingsOfUniverses α (𝒪 R) ≅ 𝒪 S :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).mapIso
      (scalarExtensionUnitRawIso α) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).counit).app (𝒪 S)

/-- The unit comparison is multiplication on scalar-extension pure sections.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: the sheafification adjunction sends the comparison back to sectionwise multiplication. -/
theorem scalarExtensionUnitIso_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (U : Cᵒᵖ) (s : S.obj.obj U) (a : R.obj.obj U) :
    ((scalarExtensionUnitIso α).hom.val.app U) (scalarExtensionSection α (𝒪 R) U s a) =
      s * α.hom.app U a := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)
  have h : adj.homEquiv _ _ (scalarExtensionUnitIso α).hom = (scalarExtensionUnitRawIso α).hom := by
    change adj.homEquiv _ _
      (_ ≫ adj.counit.app (𝒪 S)) = _
    simp only [Functor.mapIso_hom]
    erw [← adj.homEquiv_counit]
    exact Equiv.apply_symm_apply _ _
  have he := congrArg
    (fun f ↦ f.app U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] a)) h
  exact he.trans (by
    change (α.hom.app U a) * s = _
    exact mul_comm _ _)


/-- Explicit tensor unit comparison, obtained from sectionwise scalar multiplication.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorLeftUnitRawIso (R : Sheaf J CommRingCat.{u}) (N : Mod R) :
    siteTensorPresheaf (𝒪 R).val N.val ≅ N.val :=
  PresheafOfModules.isoMk (fun U ↦ (TensorProduct.lid (R.obj.obj U) (N.val.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a x
      change (R.obj.map i a) • (N.val.map i x) = N.val.map i (a • x)
      exact (N.val.map_smul i a x).symm)

/-- Explicit tensor unit comparison, obtained from sectionwise scalar multiplication.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorLeftUnitor (R : Sheaf J CommRingCat.{u}) (N : Mod R) :
    𝒯 (𝒪 R) N ≅ N :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).mapIso
      (scalarTensorLeftUnitRawIso R N) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).counit).app N

/-- The tensor unit comparison sends a pure tensor to scalar multiplication.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: the sheafification adjunction identifies the comparison with sectionwise multiplication. -/
theorem scalarTensorLeftUnitor_tmul (R : Sheaf J CommRingCat.{u}) (N : Mod R)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U) :
    ((scalarTensorLeftUnitor R N).hom.val.app U) (siteSheafTensorTmul (𝒪 R) N U a x) =
      a • x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h : adj.homEquiv _ _ (scalarTensorLeftUnitor R N).hom =
      (scalarTensorLeftUnitRawIso R N).hom := by
    change adj.homEquiv _ _ (_ ≫ adj.counit.app N) = _
    simp only [Functor.mapIso_hom]
    erw [← adj.homEquiv_counit]
    exact Equiv.apply_symm_apply _ _
  exact congrArg (fun f ↦ f.app U (a ⊗ₜ[R.obj.obj U] x)) h

/-- Explicit tensor unit comparison, obtained from sectionwise scalar multiplication.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorRightUnitRawIso (R : Sheaf J CommRingCat.{u}) (N : Mod R) :
    siteTensorPresheaf N.val (𝒪 R).val ≅ N.val :=
  PresheafOfModules.isoMk (fun U ↦ (TensorProduct.rid (R.obj.obj U) (N.val.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x a
      change (R.obj.map i a) • (N.val.map i x) = N.val.map i (a • x)
      exact (N.val.map_smul i a x).symm)

/-- Explicit tensor unit comparison, obtained from sectionwise scalar multiplication.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorRightUnitor (R : Sheaf J CommRingCat.{u}) (N : Mod R) :
    𝒯 N (𝒪 R) ≅ N :=
  (PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).mapIso
      (scalarTensorRightUnitRawIso R N) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).counit).app N

/-- The tensor unit comparison sends a pure tensor to scalar multiplication.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: the sheafification adjunction identifies the comparison with sectionwise multiplication. -/
theorem scalarTensorRightUnitor_tmul (R : Sheaf J CommRingCat.{u}) (N : Mod R)
    (U : Cᵒᵖ) (x : N.val.obj U) (a : R.obj.obj U) :
    ((scalarTensorRightUnitor R N).hom.val.app U) (siteSheafTensorTmul N (𝒪 R) U x a) =
      a • x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h : adj.homEquiv _ _ (scalarTensorRightUnitor R N).hom =
      (scalarTensorRightUnitRawIso R N).hom := by
    change adj.homEquiv _ _ (_ ≫ adj.counit.app N) = _
    simp only [Functor.mapIso_hom]
    erw [← adj.homEquiv_counit]
    exact Equiv.apply_symm_apply _ _
  exact congrArg (fun f ↦ f.app U (x ⊗ₜ[R.obj.obj U] a)) h

/-- scalarTensorSwapRawIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorSwapRawIso {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorPresheaf P Q ≅ siteTensorPresheaf Q P :=
  PresheafOfModules.isoMk
    (fun U ↦ (TensorProduct.comm (R.obj.obj U) (P.obj U) (Q.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      rfl)

/-- scalarTensorAssocRawIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorAssocRawIso {R : Sheaf J CommRingCat.{u}}
    (P Q Z : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    siteTensorPresheaf (siteTensorPresheaf P Q) Z ≅
      siteTensorPresheaf P (siteTensorPresheaf Q Z) :=
  PresheafOfModules.isoMk
    (fun U ↦ (TensorProduct.assoc (R.obj.obj U) (P.obj U) (Q.obj U) (Z.obj U)).toModuleIso)
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro xy z
      induction xy using TensorProduct.induction_on with
      | zero => simp
      | add xy xy' h h' => simp only [map_add, TensorProduct.add_tmul, h, h']
      | tmul x y => rfl)

/-- scalarSheafificationUnit for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarSheafificationUnit
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app P

/-- scalarSheafificationUnit locallyInjective for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
instance scalarSheafificationUnit_locallyInjective
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallyInjective J (scalarSheafificationUnit (J := J) P) := by
  change PresheafOfModules.IsLocallyInjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

/-- scalarSheafificationUnit locallySurjective for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
instance scalarSheafificationUnit_locallySurjective
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    (P : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.IsLocallySurjective J (scalarSheafificationUnit (J := J) P) := by
  change PresheafOfModules.IsLocallySurjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarSheafification map unit for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarSheafification_map_unit
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}] {R : Sheaf J CommRingCat.{u}}
    {P Q : PresheafOfModules.{m} (R.obj ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q)
    (U : Cᵒᵖ) (x : P.obj U) :
    (((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).map f).val.app U)
      ((scalarSheafificationUnit P).app U x) = (scalarSheafificationUnit Q).app U (f.app U x) := by
  exact (congrArg (fun g ↦ g.app U x)
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.naturality f)).symm

/-- scalarTensorSheafifyFirst isIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorSheafifyFirst_isIso {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    IsIso ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).map
        (siteTensorHom (scalarSheafificationUnit P) Q)) := by
  exact PresheafOfModules.sheafification_tensorHom_isIso
    (f := scalarSheafificationUnit P) (N := Q)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property

/-- scalarTensorSheafifyFirstIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorSheafifyFirstIso {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj
        (siteTensorPresheaf P Q)) ≅
    ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj
        (siteTensorPresheaf
          ((PresheafOfModules.sheafification
            (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val Q)) := by
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let f := siteTensorHom (scalarSheafificationUnit P) Q
  have : IsIso (L.map f) := scalarTensorSheafifyFirst_isIso P Q
  exact asIso (L.map f)

/-- scalarTensorSheafifySecondIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorSheafifySecondIso {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj
        (siteTensorPresheaf Q P)) ≅
    ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj
        (siteTensorPresheaf Q
          ((PresheafOfModules.sheafification
            (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val)) :=
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  L.mapIso (scalarTensorSwapRawIso Q P) ≪≫
    scalarTensorSheafifyFirstIso P Q ≪≫
      L.mapIso (scalarTensorSwapRawIso (L.obj P).val Q)

/-- scalarTensorAssociatorIso for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorAssociatorIso (R : Sheaf J CommRingCat.{u}) (N P Q : Mod R) :
    (siteSheafTensorRight Q).obj ((siteSheafTensorRight P).obj N) ≅ 𝒯 N (𝒯 P Q) :=
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  (scalarTensorSheafifyFirstIso (siteTensorPresheaf N.val P.val) Q.val).symm ≪≫
    L.mapIso (scalarTensorAssocRawIso N.val P.val Q.val) ≪≫
      scalarTensorSheafifySecondIso (siteTensorPresheaf P.val Q.val) N.val

/-- scalarTensorSheafifyFirstIso hom tmul for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorSheafifyFirstIso_hom_tmul {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U) :
    ((scalarTensorSheafifyFirstIso P Q).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf P Q)).app U (x ⊗ₜ[R.obj.obj U] y)) =
      (scalarSheafificationUnit (siteTensorPresheaf
        ((PresheafOfModules.sheafification
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val Q)).app U
        ((scalarSheafificationUnit P).app U x ⊗ₜ[R.obj.obj U] y) := by
  exact scalarSheafification_map_unit (siteTensorHom (scalarSheafificationUnit P) Q)
    U (x ⊗ₜ[R.obj.obj U] y)

/-- scalarTensorSheafifyFirstIso inv tmul for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorSheafifyFirstIso_inv_tmul {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U) :
    ((scalarTensorSheafifyFirstIso P Q).inv.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf
        ((PresheafOfModules.sheafification
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val Q)).app U
        ((scalarSheafificationUnit P).app U x ⊗ₜ[R.obj.obj U] y)) =
      ((scalarSheafificationUnit (siteTensorPresheaf P Q)).app U (x ⊗ₜ[R.obj.obj U] y)) := by
  rw [← scalarTensorSheafifyFirstIso_hom_tmul P Q U x y]
  change (((scalarTensorSheafifyFirstIso P Q).hom ≫
    (scalarTensorSheafifyFirstIso P Q).inv).val.app U) _ = _
  rw [Iso.hom_inv_id]
  rfl

/-- scalarTensorSheafifySecondIso hom tmul for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorSheafifySecondIso_hom_tmul {R : Sheaf J CommRingCat.{u}}
    (P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U) :
    ((scalarTensorSheafifySecondIso P Q).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf Q P)).app U (y ⊗ₜ[R.obj.obj U] x)) =
      (scalarSheafificationUnit (siteTensorPresheaf Q
        ((PresheafOfModules.sheafification
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val)).app U
        (y ⊗ₜ[R.obj.obj U] (scalarSheafificationUnit P).app U x) := by
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  change ((L.map (scalarTensorSwapRawIso (L.obj P).val Q).hom).val.app U)
    (((scalarTensorSheafifyFirstIso P Q).hom.val.app U)
      (((L.map (scalarTensorSwapRawIso Q P).hom).val.app U)
        ((scalarSheafificationUnit (siteTensorPresheaf Q P)).app U
          (y ⊗ₜ[R.obj.obj U] x)))) = _
  rw [scalarSheafification_map_unit]
  change ((L.map (scalarTensorSwapRawIso (L.obj P).val Q).hom).val.app U)
    (((scalarTensorSheafifyFirstIso P Q).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf P Q)).app U
        (x ⊗ₜ[R.obj.obj U] y))) = _
  rw [scalarTensorSheafifyFirstIso_hom_tmul, scalarSheafification_map_unit]
  rfl

/-- scalarTensorAssociatorIso tmul for the explicit sheaf tensor construction.
Source: Stacks, Tags 03EK and 05V4
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation, naturality of the sheafification unit, and tensor descent
identify the displayed maps on pure tensors; the isomorphism identities give the inverse formula. -/
theorem scalarTensorAssociatorIso_tmul (R : Sheaf J CommRingCat.{u}) (N P Q : Mod R)
    (U : Cᵒᵖ) (x : N.val.obj U) (y : P.val.obj U) (z : Q.val.obj U) :
    ((scalarTensorAssociatorIso R N P Q).hom.val.app U)
        (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z) =
      siteSheafTensorTmul N (𝒯 P Q) U x (siteSheafTensorTmul P Q U y z) := by
  let L := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  change ((scalarTensorSheafifySecondIso (siteTensorPresheaf P.val Q.val) N.val).hom.val.app U)
    (((L.map (scalarTensorAssocRawIso N.val P.val Q.val).hom).val.app U)
      (((scalarTensorSheafifyFirstIso (siteTensorPresheaf N.val P.val) Q.val).inv.val.app U)
        ((scalarSheafificationUnit
          (siteTensorPresheaf (𝒯 N P).val Q.val)).app U
            ((scalarSheafificationUnit (siteTensorPresheaf N.val P.val)).app U
              (x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)))) = _
  erw [scalarTensorSheafifyFirstIso_inv_tmul (R := R)
    (siteTensorPresheaf N.val P.val) Q.val U (x ⊗ₜ[R.obj.obj U] y) z]
  rw [scalarSheafification_map_unit]
  change ((scalarTensorSheafifySecondIso (siteTensorPresheaf P.val Q.val) N.val).hom.val.app U)
    ((scalarSheafificationUnit (siteTensorPresheaf N.val
      (siteTensorPresheaf P.val Q.val))).app U (x ⊗ₜ[R.obj.obj U] (y ⊗ₜ[R.obj.obj U] z))) = _
  rw [scalarTensorSheafifySecondIso_hom_tmul]
  rfl

/-- The actual sheaf tensor coherence, constructed without choosing existence witnesses.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def scalarTensorCoherence (R : Sheaf J CommRingCat.{u}) :
    ScalarTensorCoherence R where
  associator := scalarTensorAssociatorIso R
  associator_tmul := scalarTensorAssociatorIso_tmul R
  leftUnitor := scalarTensorLeftUnitor R
  leftUnitor_tmul := scalarTensorLeftUnitor_tmul R
  rightUnitor := scalarTensorRightUnitor R
  rightUnitor_tmul := scalarTensorRightUnitor_tmul R

/-- The binary part of scalar extension, before forming any tensor powers.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
structure ScalarExtensionTensorCore
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) where
  tensorComparison : ∀ (N P : Mod R),
    changeOfRingsOfUniverses α (𝒯 N P) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N)
  tensor_tmul : ∀ (N P : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U)
      (x : N.val.obj U) (y : P.val.obj U),
    ((tensorComparison N P).hom.val.app U)
        (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y)
  associator_compat : ∀ (N P Q : Mod R),
    changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).associator N P Q).hom ≫
        (tensorComparison N (𝒯 P Q)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N)
          (tensorComparison P Q).hom =
      (tensorComparison (𝒯 N P) Q).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α Q)).map
          (tensorComparison N P).hom ≫
        ((scalarTensorCoherence S).associator (changeOfRingsOfUniverses α N)
          (changeOfRingsOfUniverses α P) (changeOfRingsOfUniverses α Q)).hom
  leftUnitor_compat : ∀ (N : Mod R),
    (tensorComparison (𝒪 R) N).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α N)).map (scalarExtensionUnitIso α).hom ≫
        ((scalarTensorCoherence S).leftUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).leftUnitor N).hom
  rightUnitor_compat : ∀ (N : Mod R),
    (tensorComparison N (𝒪 R)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N) (scalarExtensionUnitIso α).hom ≫
        ((scalarTensorCoherence S).rightUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).rightUnitor N).hom
  tensor_natural : ∀ {N N' P P' : Mod R} (f : N ⟶ N') (g : P ⟶ P'),
    changeOfRingsHomOfUniverses α _
        ((siteSheafTensorRight P).map f ≫ siteSheafTensorSecondMap N' g) ≫
        (tensorComparison N' P').hom =
      (tensorComparison N P).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α P)).map
          (changeOfRingsHomOfUniverses α N f) ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N')
          (changeOfRingsHomOfUniverses α P g)

/-- Source tensor coherence with the explicitly constructed unitors.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def ScalarExtensionTensorCore.sourceCoherence
    {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}
    (_e : ScalarExtensionTensorCore R S α) : ScalarTensorCoherence R :=
  scalarTensorCoherence R

/-- Target tensor coherence with the explicitly constructed unitors.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def ScalarExtensionTensorCore.targetCoherence
    {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}
    (_e : ScalarExtensionTensorCore R S α) : ScalarTensorCoherence S :=
  scalarTensorCoherence S

/-- The unit comparison is the explicit multiplication construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def ScalarExtensionTensorCore.unitComparison
    {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}
    (_e : ScalarExtensionTensorCore R S α) :
    changeOfRingsOfUniverses α (𝒪 R) ≅ 𝒪 S := scalarExtensionUnitIso α

/-- Normalization of the explicit unit comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: this is the multiplication formula already proved for the constructed comparison. -/
theorem ScalarExtensionTensorCore.unit_tmul
    {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}
    (e : ScalarExtensionTensorCore R S α)
    (U : Cᵒᵖ) (s : S.obj.obj U) (a : R.obj.obj U) :
    (e.unitComparison.hom.val.app U) (scalarExtensionSection α (𝒪 R) U s a) =
      s * α.hom.app U a := scalarExtensionUnitIso_tmul α U s a

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtension_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_hom_ext
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S)} (f g : changeOfRingsOfUniverses α N ⟶ H)
    (h : ∀ U s x, f.val.app U (scalarExtensionSection α N U s x) =
      g.val.app U (scalarExtensionSection α N U s x)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U 1 x

/-- scalarTensor_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensor_hom_ext {R : Sheaf J CommRingCat.{u}}
    (N P : Mod R) {H : Mod R} (f g : 𝒯 N P ⟶ H)
    (h : ∀ U x y, f.val.app U (siteSheafTensorTmul N P U x y) =
      g.val.app U (siteSheafTensorTmul N P U x y)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact h U x y

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_naturality for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_naturality
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsOfUniverses α N).val.map i (scalarExtensionSection α N U s x) =
      scalarExtensionSection α N V (S.obj.map i s) (N.val.map i x) := by
  have h := (PresheafOfModules.naturality_apply
    (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)) i
      (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)).symm
  exact h.trans (congrArg ((scalarSheafificationUnit
    (changeOfRingsPresheafOfUniverses α N)).app V)
      (changeOfRingsMap_tmulOfUniverses α N i s x))

/-- scalarTensorTmul_naturality for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_naturality {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : N.val.obj U) (y : P.val.obj U) :
    (𝒯 N P).val.map i (siteSheafTensorTmul N P U x y) =
      siteSheafTensorTmul N P V (N.val.map i x) (P.val.map i y) := by
  exact (PresheafOfModules.naturality_apply
    (scalarSheafificationUnit (siteTensorPresheaf N.val P.val)) i
      (x ⊗ₜ[R.obj.obj U] y)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtension_map_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_map_tmul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    {N P : SheafOfModules.{m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)} (f : N ⟶ P)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (changeOfRingsHomOfUniverses α N f).val.app U (scalarExtensionSection α N U s x) =
      scalarExtensionSection α P U s (f.val.app U x) := by
  exact scalarSheafification_map_unit
    ({ app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
       naturality := changeOfRingsHom_naturalityOfUniverses α N f } :
      changeOfRingsPresheafOfUniverses α N ⟶ changeOfRingsPresheafOfUniverses α P)
    U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)

/-- scalarTensor_first_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensor_first_tmul {R : Sheaf J CommRingCat.{u}}
    {N N' : Mod R} (f : N ⟶ N') (P : Mod R) (U : Cᵒᵖ)
    (x : N.val.obj U) (y : P.val.obj U) :
    ((siteSheafTensorRight P).map f).val.app U (siteSheafTensorTmul N P U x y) =
      siteSheafTensorTmul N' P U (f.val.app U x) y :=
  scalarSheafification_map_unit (siteTensorHom f.val P.val) U (x ⊗ₜ[R.obj.obj U] y)

/-- scalarTensor_second_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensor_second_tmul {R : Sheaf J CommRingCat.{u}}
    (N : Mod R) {P P' : Mod R} (g : P ⟶ P') (U : Cᵒᵖ)
    (x : N.val.obj U) (y : P.val.obj U) :
    (siteSheafTensorSecondMap N g).val.app U (siteSheafTensorTmul N P U x y) =
      siteSheafTensorTmul N P' U x (g.val.app U y) :=
  scalarSheafification_map_unit (siteTensorSecondMap N.val g.val) U (x ⊗ₜ[R.obj.obj U] y)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_add for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_add
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x y : N.val.obj U) :
    scalarExtensionSection α N U s (x + y) =
      scalarExtensionSection α N U s x + scalarExtensionSection α N U s y := by
  dsimp only [scalarExtensionSection]
  rw [TensorProduct.tmul_add, map_add]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_zero for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_zero
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) :
    scalarExtensionSection α N U s 0 = 0 := by
  dsimp only [scalarExtensionSection]
  rw [TensorProduct.tmul_zero, map_zero]

/-- scalarExtension_tensor_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_tensor_hom_ext {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) {H : Mod S} (f g : changeOfRingsOfUniverses α (𝒯 N P) ⟶ H)
    (h : ∀ U s x y, f.val.app U
        (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      g.val.app U
        (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y))) :
    f = g := by
  apply scalarExtension_hom_ext α (𝒯 N P)
  intro U s z
  let η := scalarSheafificationUnit (siteTensorPresheaf N.val P.val)
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (𝒯 N P).val.map i.op z at ht
  change H.val.map i.op (f.val.app U _) = H.val.map i.op (g.val.app U _)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val, scalarExtensionSection_naturality, ← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, scalarExtensionSection_zero]
  | add t t' ih ih' =>
    simp only [map_add, scalarExtensionSection_add, ih, ih']
  | tmul x y => exact h (op V) (S.obj.map i.op s) x y

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_smul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_smul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s t : S.obj.obj U) (x : N.val.obj U) :
    s • scalarExtensionSection α N U t x = scalarExtensionSection α N U (s * t) x := by
  let η := ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (changeOfRingsPresheafOfUniverses α N)).app U
  exact (η.hom.map_smul s (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionSection_base_smul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionSection_base_smul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (a : R.obj.obj U) (x : N.val.obj U) :
    scalarExtensionSection α N U s (a • x) =
      scalarExtensionSection α N U (s * α.hom.app U a) x := by
  dsimp only [scalarExtensionSection]
  congr 1
  rw [TensorProduct.tmul_smul]
  exact congrArg (fun z : S.obj.obj U ↦ z ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)
    (mul_comm (α.hom.app U a) s)

/-- scalarTensorTmul_add_first for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_add_first {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    (U : Cᵒᵖ) (x x' : N.val.obj U) (y : P.val.obj U) :
    siteSheafTensorTmul N P U (x + x') y =
      siteSheafTensorTmul N P U x y + siteSheafTensorTmul N P U x' y := by
  dsimp only [siteSheafTensorTmul]
  rw [TensorProduct.add_tmul, map_add]

/-- scalarTensorTmul_zero_first for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_zero_first {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    (U : Cᵒᵖ) (y : P.val.obj U) : siteSheafTensorTmul N P U 0 y = 0 := by
  dsimp only [siteSheafTensorTmul]
  rw [TensorProduct.zero_tmul, map_zero]

/-- scalarExtension_tensor3_hom_ext for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtension_tensor3_hom_ext {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P Q : Mod R) {H : Mod S} (f g : changeOfRingsOfUniverses α ((siteSheafTensorRight Q).obj
      ((siteSheafTensorRight P).obj N)) ⟶ H)
    (h : ∀ U s x y z, f.val.app U
        (scalarExtensionSection α ((siteSheafTensorRight Q).obj ((siteSheafTensorRight P).obj N))
          U s
          (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z)) =
      g.val.app U (scalarExtensionSection α ((siteSheafTensorRight Q).obj ((siteSheafTensorRight
        P).obj N)) U s
          (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z))) :
    f = g := by
  apply scalarExtension_tensor_hom_ext α (𝒯 N P) Q
  intro U s xy z
  let η := scalarSheafificationUnit (siteTensorPresheaf N.val P.val)
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) xy)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (𝒯 N P).val.map i.op xy at ht
  change H.val.map i.op (f.val.app U _) = H.val.map i.op (g.val.app U _)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val, scalarExtensionSection_naturality,
    scalarTensorTmul_naturality, ← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, scalarTensorTmul_zero_first, scalarExtensionSection_zero]
  | add t t' ih ih' =>
    simp only [map_add, scalarTensorTmul_add_first, scalarExtensionSection_add, ih, ih']
  | tmul x y => exact h (op V) (S.obj.map i.op s) x y (Q.val.map i.op z)

section Coherence
variable {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (k : ∀ N P : Mod R, changeOfRingsOfUniverses α (𝒯 N P) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N))
    (hk : ∀ N P U s x y, ((k N P).hom.val.app U)
      (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y))

include hk

/-- scalarTensorComparison_associator for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorComparison_associator (N P Q : Mod R) :
    changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).associator N P Q).hom ≫
        (k N (𝒯 P Q)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N) (k P Q).hom =
      (k (𝒯 N P) Q).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α Q)).map (k N P).hom ≫
        ((scalarTensorCoherence S).associator (changeOfRingsOfUniverses α N)
          (changeOfRingsOfUniverses α P) (changeOfRingsOfUniverses α Q)).hom := by
  apply scalarExtension_tensor3_hom_ext α N P Q
  intro U s x y z
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtension_map_tmul, scalarTensorCoherence, scalarTensorAssociatorIso_tmul,
    hk, scalarTensor_first_tmul, scalarTensor_second_tmul]

/-- scalarTensorComparison_leftUnitor for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorComparison_leftUnitor (N : Mod R) :
    (k (𝒪 R) N).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α N)).map
          (scalarExtensionUnitIso α).hom ≫
        ((scalarTensorCoherence S).leftUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).leftUnitor N).hom := by
  apply scalarExtension_tensor_hom_ext α (𝒪 R) N
  intro U s a x
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, hk,
    scalarTensor_first_tmul, scalarExtensionUnitIso_tmul, scalarTensorCoherence,
    scalarTensorLeftUnitor_tmul, scalarExtension_map_tmul]
  rw [scalarExtensionSection_base_smul, scalarExtensionSection_smul, mul_one]

/-- scalarTensorComparison_rightUnitor for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorComparison_rightUnitor (N : Mod R) :
    (k N (𝒪 R)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N)
          (scalarExtensionUnitIso α).hom ≫
        ((scalarTensorCoherence S).rightUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ ((scalarTensorCoherence R).rightUnitor N).hom := by
  apply scalarExtension_tensor_hom_ext α N (𝒪 R)
  intro U s x a
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, hk,
    scalarTensor_second_tmul, scalarExtensionUnitIso_tmul, scalarTensorCoherence,
    scalarTensorRightUnitor_tmul, scalarExtension_map_tmul, one_mul]
  rw [scalarExtensionSection_base_smul, scalarExtensionSection_smul, mul_comm]

/-- scalarTensorComparison_natural for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorComparison_natural {N N' P P' : Mod R} (f : N ⟶ N') (g : P ⟶ P') :
    changeOfRingsHomOfUniverses α _
        ((siteSheafTensorRight P).map f ≫ siteSheafTensorSecondMap N' g) ≫
        (k N' P').hom =
      (k N P).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α P)).map
          (changeOfRingsHomOfUniverses α N f) ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N')
          (changeOfRingsHomOfUniverses α P g) := by
  apply scalarExtension_tensor_hom_ext α N P
  intro U s x y
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtension_map_tmul, scalarTensor_first_tmul, scalarTensor_second_tmul, hk]
end Coherence

/-- scalarTensorBinaryInverseApp for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryInverseApp {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) :
    (siteTensorPresheaf (changeOfRingsPresheafOfUniverses α N)
      (changeOfRingsPresheafOfUniverses α P)).obj U ⟶
      (changeOfRingsPresheafOfUniverses α (𝒯 N P)).obj U := by
  letI := (α.hom.app U).hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange
    (R.obj.obj U) (S.obj.obj U) (N.val.obj U) (P.val.obj U)).symm.toModuleIso.hom ≫
      (ModuleCat.extendScalars (α.hom.app U).hom).map
        ((scalarSheafificationUnit (siteTensorPresheaf N.val P.val)).app U)

/-- scalarTensorBinaryInverseApp_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryInverseApp_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) (s t : S.obj.obj U)
    (x : N.val.obj U) (y : P.val.obj U) :
    scalarTensorBinaryInverseApp α N P U
      ((s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x) ⊗ₜ[S.obj.obj U]
        (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] y)) =
      (s * t) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] (siteSheafTensorTmul N P U x y) := by
  let := (α.hom.app U).hom.toAlgebra
  change (ModuleCat.extendScalars (α.hom.app U).hom).map
    ((scalarSheafificationUnit (siteTensorPresheaf N.val P.val)).app U)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange
      (R.obj.obj U) (S.obj.obj U) (N.val.obj U) (P.val.obj U)).symm
      ((s ⊗ₜ[R.obj.obj U] x) ⊗ₜ[S.obj.obj U] (t ⊗ₜ[R.obj.obj U] y))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
  rfl

/-- scalarTensorBinaryRawInverse for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryRawInverse {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    siteTensorPresheaf (changeOfRingsPresheafOfUniverses α N)
        (changeOfRingsPresheafOfUniverses α P) ⟶
      changeOfRingsPresheafOfUniverses α (𝒯 N P) where
  app U := scalarTensorBinaryInverseApp α N P U
  naturality := by
    intro U V i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
    | tmul s x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, hy, hy']
      | tmul t y =>
        change scalarTensorBinaryInverseApp α N P V
          (changeOfRingsMapOfUniverses α N i (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)
            ⊗ₜ[S.obj.obj V] changeOfRingsMapOfUniverses α P i
              (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] y)) =
          changeOfRingsMapOfUniverses α (𝒯 N P) i
            (scalarTensorBinaryInverseApp α N P U
              ((s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x) ⊗ₜ[S.obj.obj U]
                (t ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] y)))
        rw [changeOfRingsMap_tmulOfUniverses, changeOfRingsMap_tmulOfUniverses,
          scalarTensorBinaryInverseApp_tmul, scalarTensorBinaryInverseApp_tmul,
          changeOfRingsMap_tmulOfUniverses, map_mul, scalarTensorTmul_naturality]


/-- scalarTensorBinaryDescentIso for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryDescentIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).obj
      (siteTensorPresheaf (changeOfRingsPresheafOfUniverses α N)
        (changeOfRingsPresheafOfUniverses α P)) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N) :=
  scalarTensorSheafifyFirstIso (changeOfRingsPresheafOfUniverses α N)
      (changeOfRingsPresheafOfUniverses α P) ≪≫
    scalarTensorSheafifySecondIso (changeOfRingsPresheafOfUniverses α P)
      (changeOfRingsOfUniverses α N).val

/-- scalarTensorBinaryDescentIso_hom for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryDescentIso_hom {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ)
    (x : (changeOfRingsPresheafOfUniverses α N).obj U)
    (y : (changeOfRingsPresheafOfUniverses α P).obj U) :
    ((scalarTensorBinaryDescentIso α N P).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf
        (changeOfRingsPresheafOfUniverses α N)
        (changeOfRingsPresheafOfUniverses α P))).app U (x ⊗ₜ[S.obj.obj U] y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        ((scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)).app U x)
        ((scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α P)).app U y) := by
  change ((scalarTensorSheafifySecondIso (changeOfRingsPresheafOfUniverses α P)
      (changeOfRingsOfUniverses α N).val).hom.val.app U)
    (((scalarTensorSheafifyFirstIso (changeOfRingsPresheafOfUniverses α N)
      (changeOfRingsPresheafOfUniverses α P)).hom.val.app U) _) = _
  rw [scalarTensorSheafifyFirstIso_hom_tmul (R := S)]
  erw [scalarTensorSheafifySecondIso_hom_tmul (R := S)]
  rfl

/-- scalarTensorBinaryInverse for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryInverse {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N) ⟶
      changeOfRingsOfUniverses α (𝒯 N P) :=
  (scalarTensorBinaryDescentIso α N P).inv ≫
    (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).map
        (scalarTensorBinaryRawInverse α N P)

/-- scalarTensorBinaryInverse_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryInverse_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) (s t : S.obj.obj U)
    (x : N.val.obj U) (y : P.val.obj U) :
    (scalarTensorBinaryInverse α N P).val.app U
      (siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U t y)) =
      scalarExtensionSection α (𝒯 N P) U (s * t) (siteSheafTensorTmul N P U x y) := by
  let := (α.hom.app U).hom.toAlgebra
  let z := (scalarSheafificationUnit (siteTensorPresheaf
    (changeOfRingsPresheafOfUniverses α N) (changeOfRingsPresheafOfUniverses α P))).app U
      ((s ⊗ₜ[R.obj.obj U] x) ⊗ₜ[S.obj.obj U] (t ⊗ₜ[R.obj.obj U] y))
  have he := scalarTensorBinaryDescentIso_hom α N P U
    (s ⊗ₜ[R.obj.obj U] x) (t ⊗ₜ[R.obj.obj U] y)
  change ((scalarTensorBinaryDescentIso α N P).hom.val.app U) z =
    siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
      (scalarExtensionSection α N U s x) (scalarExtensionSection α P U t y) at he
  rw [← he]
  unfold scalarTensorBinaryInverse
  change (((scalarTensorBinaryDescentIso α N P).hom ≫
    (scalarTensorBinaryDescentIso α N P).inv ≫
    (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).map
        (scalarTensorBinaryRawInverse α N P)).val.app U) z = _
  rw [Iso.hom_inv_id_assoc]
  dsimp only [z]
  rw [scalarSheafification_map_unit]
  exact congrArg ((scalarSheafificationUnit
    (changeOfRingsPresheafOfUniverses α (𝒯 N P))).app U)
      (scalarTensorBinaryInverseApp_tmul α N P U s t x y)



/-- scalarTensorTmul_smul_first for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_smul_first {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U) (y : P.val.obj U) :
    siteSheafTensorTmul N P U (a • x) y = a • siteSheafTensorTmul N P U x y := by
  dsimp only [siteSheafTensorTmul]
  rw [← TensorProduct.smul_tmul', map_smul]

/-- scalarTensorTmul_smul_second for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorTmul_smul_second {R : Sheaf J CommRingCat.{u}} (N P : Mod R)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U) (y : P.val.obj U) :
    siteSheafTensorTmul N P U x (a • y) = a • siteSheafTensorTmul N P U x y := by
  dsimp only [siteSheafTensorTmul]
  erw [TensorProduct.tmul_smul, map_smul]

/-- scalarTensorBinaryPair for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryPair {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) :
    N.val.obj U →ₗ[R.obj.obj U] P.val.obj U →ₗ[R.obj.obj U]
      (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
          N))).val.obj U) := by
  let H := ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
    N))
  let : Module (R.obj.obj U) (H.val.obj U) :=
    Module.compHom (H.val.obj U) (α.hom.app U).hom
  apply LinearMap.mk₂ (R.obj.obj U)
    (fun x y ↦ siteSheafTensorTmul (changeOfRingsOfUniverses α N)
      (changeOfRingsOfUniverses α P) U
      (scalarExtensionSection α N U 1 x) (scalarExtensionSection α P U 1 y))
  · intro x x' y
    dsimp only [siteSheafTensorTmul]
    rw [scalarExtensionSection_add, TensorProduct.add_tmul, map_add]
  · intro a x y
    change siteSheafTensorTmul _ _ U (scalarExtensionSection α N U 1 (a • x)) _ =
      α.hom.app U a • siteSheafTensorTmul _ _ U _ _
    rw [scalarExtensionSection_base_smul, one_mul,
      ← scalarTensorTmul_smul_first, scalarExtensionSection_smul, mul_one]
  · intro x y y'
    dsimp only [siteSheafTensorTmul]
    rw [scalarExtensionSection_add, TensorProduct.tmul_add, map_add]
  · intro a x y
    change siteSheafTensorTmul _ _ U _ (scalarExtensionSection α P U 1 (a • y)) =
      α.hom.app U a • siteSheafTensorTmul _ _ U _ _
    rw [scalarExtensionSection_base_smul, one_mul,
      ← scalarTensorTmul_smul_second, scalarExtensionSection_smul, mul_one]

/-- scalarTensorBinaryRawForward for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryRawForward {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    siteTensorPresheaf N.val P.val ⟶
      (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
          N))).val) where
  app U := ModuleCat.ofHom (Y :=
    (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
        N))).val.obj U))
    (TensorProduct.lift (scalarTensorBinaryPair α N P U))
  naturality := by
    intro U V i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change siteSheafTensorTmul _ _ V
      (scalarExtensionSection α N V 1 (N.val.map i x))
      (scalarExtensionSection α P V 1 (P.val.map i y)) =
        ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α
          N)).val.map i
          (siteSheafTensorTmul _ _ U (scalarExtensionSection α N U 1 x)
            (scalarExtensionSection α P U 1 y))
    rw [scalarTensorTmul_naturality, scalarExtensionSection_naturality,
      scalarExtensionSection_naturality, map_one]

/-- scalarTensorBinaryBaseForward for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryBaseForward {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    𝒯 N P ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N)) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).homEquiv _ _).symm
      (scalarTensorBinaryRawForward α N P)

/-- scalarTensorBinaryBaseForward_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryBaseForward_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) (x : N.val.obj U) (y : P.val.obj U) :
    (scalarTensorBinaryBaseForward α N P).val.app U (siteSheafTensorTmul N P U x y) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U 1 x) (scalarExtensionSection α P U 1 y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h : adj.homEquiv (siteTensorPresheaf N.val P.val)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        ((siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N)))
      (scalarTensorBinaryBaseForward α N P) = scalarTensorBinaryRawForward α N P :=
    Equiv.apply_symm_apply _ _
  exact congrArg (fun f ↦ f.app U (x ⊗ₜ[R.obj.obj U] y)) h

/-- scalarExtensionRawLift for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarExtensionRawLift
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H) :
    changeOfRingsPresheafOfUniverses α N ⟶ H.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (α.hom.app U).hom (f.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (α.hom.app V).hom (f.val.app V)
        (changeOfRingsMapOfUniverses α N i
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) = _
    rw [changeOfRingsMap_tmulOfUniverses, map_one]
    change (1 : S.obj.obj V) • (show H.val.obj V from f.val.app V (N.val.map i x)) =
      H.val.map i ((1 : S.obj.obj U) • (show H.val.obj U from f.val.app U x))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply f.val i x

/-- scalarExtensionLift for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarExtensionLift
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H) :
    changeOfRingsOfUniverses α N ⟶ H :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _).symm
      (scalarExtensionRawLift α N H f)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionLift_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarExtensionLift_tmul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}] {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S))
    (f : N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj H)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) :
    (scalarExtensionLift α N H f).val.app U (scalarExtensionSection α N U s x) =
      s • (show H.val.obj U from f.val.app U x) := by
  have h := congrArg (fun g ↦ g.app U (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x))
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _
        |>.apply_symm_apply (scalarExtensionRawLift α N H f))
  refine h.trans ?_
  rfl

/-- scalarTensorBinaryForward for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryForward {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    changeOfRingsOfUniverses α (𝒯 N P) ⟶
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N) :=
  scalarExtensionLift α (𝒯 N P) _ (scalarTensorBinaryBaseForward α N P)

/-- scalarTensorBinaryForward_tmul for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryForward_tmul {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) (y : P.val.obj U) :
    (scalarTensorBinaryForward α N P).val.app U
      (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y) := by
  rw [scalarTensorBinaryForward, scalarExtensionLift_tmul, scalarTensorBinaryBaseForward_tmul]
  rw [← scalarTensorTmul_smul_first, scalarExtensionSection_smul, mul_one]


/-- scalarTensorBinaryForward_inverse for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryForward_inverse {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    scalarTensorBinaryForward α N P ≫ scalarTensorBinaryInverse α N P = 𝟙 _ := by
  apply scalarExtension_tensor_hom_ext α N P
  intro U s x y
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarTensorBinaryForward_tmul, scalarTensorBinaryInverse_tmul, mul_one,
    id_val, PresheafOfModules.id_app, ModuleCat.id_apply]

/-- scalarTensorBinaryInverse_forward for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: tensor generation and the sheafification adjunction reduce the assertion to the
pure-tensor formulas; scalar balancing and the isomorphism identities give the result.
-/
theorem scalarTensorBinaryInverse_forward {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    scalarTensorBinaryInverse α N P ≫ scalarTensorBinaryForward α N P = 𝟙 _ := by
  apply (cancel_epi (scalarTensorBinaryDescentIso α N P).hom).1
  simp only [Category.comp_id]
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _
      |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro z w
  change (scalarTensorBinaryForward α N P).val.app U
    ((scalarTensorBinaryInverse α N P).val.app U
      (((scalarTensorBinaryDescentIso α N P).hom.val.app U)
        ((scalarSheafificationUnit (siteTensorPresheaf
          (changeOfRingsPresheafOfUniverses α N)
          (changeOfRingsPresheafOfUniverses α P))).app U (z ⊗ₜ[S.obj.obj U] w)))) =
    ((scalarTensorBinaryDescentIso α N P).hom.val.app U)
      ((scalarSheafificationUnit (siteTensorPresheaf
        (changeOfRingsPresheafOfUniverses α N)
        (changeOfRingsPresheafOfUniverses α P))).app U (z ⊗ₜ[S.obj.obj U] w))
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add z z' hz hz' => simp only [TensorProduct.add_tmul, map_add, hz, hz']
  | tmul s x =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | tmul t y =>
      change S.obj.obj U at s t
      rw [scalarTensorBinaryDescentIso_hom]
      change (scalarTensorBinaryForward α N P).val.app U
        ((scalarTensorBinaryInverse α N P).val.app U
          (siteSheafTensorTmul _ _ U (scalarExtensionSection α N U s x)
            (scalarExtensionSection α P U t y))) = _
      rw [scalarTensorBinaryInverse_tmul, scalarTensorBinaryForward_tmul]
      change siteSheafTensorTmul _ _ U (scalarExtensionSection α N U (s * t) x)
        (scalarExtensionSection α P U 1 y) =
          siteSheafTensorTmul _ _ U (scalarExtensionSection α N U s x)
            (scalarExtensionSection α P U t y)
      rw [mul_comm s t, ← scalarExtensionSection_smul α N U t s,
        scalarTensorTmul_smul_first]
      have ht := scalarExtensionSection_smul α P U t 1 y
      rw [mul_one] at ht
      rw [← ht, scalarTensorTmul_smul_second]

/-- scalarTensorBinaryIso for the normalized binary comparison.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
-/
noncomputable def scalarTensorBinaryIso {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N P : Mod R) :
    changeOfRingsOfUniverses α (𝒯 N P) ≅
      (siteSheafTensorRight (changeOfRingsOfUniverses α P)).obj (changeOfRingsOfUniverses α N) where
  hom := scalarTensorBinaryForward α N P
  inv := scalarTensorBinaryInverse α N P
  hom_inv_id := scalarTensorBinaryForward_inverse α N P
  inv_hom_id := scalarTensorBinaryInverse_forward α N P



/-- The pure-tensor normalization determines the binary comparison uniquely.
Source: Stacks Project, Tag 03EK (blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: the scalar-extension and tensor generators determine every map out of the source. -/
theorem scalarExtensionTensorCore_subsingleton
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) :
    Subsingleton (ScalarExtensionTensorCore R S α) := by
  constructor
  intro e f
  have he : e.tensorComparison = f.tensorComparison := by
    funext N P
    apply Iso.ext
    apply scalarExtension_tensor_hom_ext α N P
    intro U s x y
    rw [e.tensor_tmul, f.tensor_tmul]
  cases e
  cases f
  cases he
  rfl

/-- Existence of normalized binary scalar-extension comparisons.
Source: Stacks Project, Tag 03EK, tensor-product formulas
(blueprint: lem-sp-scalar-extension-binary-coherence).

Proof: construct the sectionwise associator and the two unitors from the tensor
universal property, and descend through module sheafification. Their inverses send
`x ⊗ (y ⊗ z)` to `(x ⊗ y) ⊗ z`, and send `x` to `1 ⊗ x` or `x ⊗ 1`.
For extension of scalars the unit comparison is `s ⊗ a ↦ s α(a)`, with inverse
`s ↦ s ⊗ 1`. The binary comparison sends `s ⊗ (x ⊗ y)` to
`(s ⊗ x) ⊗ (1 ⊗ y)`. Its inverse sends `(s ⊗ x) ⊗ (t ⊗ y)` to
`st ⊗ (x ⊗ y)`. Balancing makes these linear maps; tensor descent through
sheafification extends them to the sheaf tensors, and their composites are identity
on pure inputs, hence identity by the sheafification universal property.
The associator square, both unitor squares, and the bifunctor naturality square
commute on pure inputs: their values use the same restricted sections and products
of scalars. Repeated tensor descent therefore proves all the required equalities.
No tensor powers, duals, flatness or rank assumptions enter this construction. -/
theorem exists_scalarExtensionTensorCore
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) :
    Nonempty (ScalarExtensionTensorCore R S α) := by
  let k := scalarTensorBinaryIso α
  have hk := scalarTensorBinaryForward_tmul α
  exact ⟨{
    tensorComparison := k
    tensor_tmul := hk
    associator_compat := scalarTensorComparison_associator α k hk
    leftUnitor_compat := scalarTensorComparison_leftUnitor α k hk
    rightUnitor_compat := scalarTensorComparison_rightUnitor α k hk
    tensor_natural := scalarTensorComparison_natural α k hk }⟩

/-- Scalar extension preserves identity morphisms.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: extension of scalars preserves identities sectionwise, and so does sheafification. -/
theorem scalarExtension_map_id {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) : changeOfRingsHomOfUniverses α N (𝟙 N) = 𝟙 _ := by
  let a := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)
  let t : changeOfRingsPresheafOfUniverses α N ⟶ changeOfRingsPresheafOfUniverses α N :=
    { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (𝟙 (N.val.obj U))
      naturality := changeOfRingsHom_naturalityOfUniverses α N (𝟙 N) }
  have ht : t = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id (N.val.obj U)
  change a.map t = 𝟙 _
  rw [ht]
  exact a.map_id _

/-- Scalar extension preserves composites of module morphisms.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: both extension of scalars on sections and module sheafification are functors. -/
theorem scalarExtension_map_comp {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    {N P Q : Mod R} (f : N ⟶ P) (g : P ⟶ Q) :
    changeOfRingsHomOfUniverses α N (f ≫ g) =
      changeOfRingsHomOfUniverses α N f ≫ changeOfRingsHomOfUniverses α P g := by
  unfold changeOfRingsHomOfUniverses
  rw [← Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp (f.val.app U) (g.val.app U)

/-- An identity in the second tensor factor induces the identity.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: `id ⊗ id` is the identity sectionwise; sheafification preserves identities. -/
theorem scalarTensor_second_id {R : Sheaf J CommRingCat.{u}} (N P : Mod R) :
    siteSheafTensorSecondMap N (𝟙 P) = 𝟙 (𝒯 N P) := by
  let a := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let t : siteTensorPresheaf N.val P.val ⟶ siteTensorPresheaf N.val P.val :=
    siteTensorSecondMap N.val (𝟙 P.val)
  have ht : t = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  change a.map t = 𝟙 _
  rw [ht]
  exact a.map_id _

namespace ScalarExtensionTensorCore

variable {R S : Sheaf J CommRingCat.{u}} {α : R ⟶ S}

/-- Binary comparison naturality with the right factor fixed.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: specialize bifunctor naturality to an identity in the second factor. -/
theorem first_natural (e : ScalarExtensionTensorCore R S α)
    {N N' : Mod R} (f : N ⟶ N') (P : Mod R) :
    changeOfRingsHomOfUniverses α _ ((siteSheafTensorRight P).map f) ≫
        (e.tensorComparison N' P).hom =
      (e.tensorComparison N P).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α P)).map
          (changeOfRingsHomOfUniverses α N f) := by
  simpa only [scalarTensor_second_id, Category.comp_id, scalarExtension_map_id] using
    e.tensor_natural f (𝟙 P)

/-- Construct power comparisons recursively from the binary comparison.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def power (e : ScalarExtensionTensorCore R S α) (N : Mod R) :
    ∀ r : ℕ, changeOfRingsOfUniverses α (scalarTensorPower R N r) ≅
      scalarTensorPower S (changeOfRingsOfUniverses α N) r
  | 0 => e.unitComparison
  | 1 => Iso.refl _
  | r + 2 => e.tensorComparison (scalarTensorPower R N (r + 1)) N ≪≫
      (siteSheafTensorRight (changeOfRingsOfUniverses α N)).mapIso (e.power N (r + 1))

/-- Naturality of the recursively constructed power comparisons.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence).
Proof: degrees zero and one are the unit and identity cases. At degree `r + 2`,
use binary naturality, commute the second-factor map with the preceding power
comparison, and apply the induction hypothesis inside the tensor functor. -/
theorem power_natural (e : ScalarExtensionTensorCore R S α)
    (N P : Mod R) (f : N ⟶ P) (r : ℕ) :
    changeOfRingsHomOfUniverses α _ (scalarTensorPowerMap R f r) ≫ (e.power P r).hom =
      (e.power N r).hom ≫ scalarTensorPowerMap S (changeOfRingsHomOfUniverses α N f) r := by
  induction r using Nat.twoStepInduction with
  | zero => simp only [scalarTensorPowerMap, power, scalarExtension_map_id,
      Category.id_comp, Category.comp_id]
  | one => simp only [scalarTensorPowerMap, scalarTensorPower, power, Iso.refl_hom,
      Category.id_comp, Category.comp_id]
  | more r _ ih =>
    simp only [scalarTensorPowerMap, power, Iso.trans_hom, Functor.mapIso_hom]
    dsimp only [scalarTensorPower]
    rw [← Category.assoc, e.tensor_natural]
    simp only [Category.assoc]
    rw [← siteSheafTensorSecondMap_naturality]
    slice_lhs 2 3 =>
      rw [← Functor.map_comp, ih, Functor.map_comp]
    simp only [Category.assoc]

/-- Extend binary comparisons to every power, with naturality proved by induction.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-binary-coherence). -/
noncomputable def withPowers (e : ScalarExtensionTensorCore R S α) :
    ScalarExtensionTensorComparison R S α where
  sourceCoherence := e.sourceCoherence
  targetCoherence := e.targetCoherence
  unitComparison := e.unitComparison
  unit_tmul := e.unit_tmul
  tensorComparison := e.tensorComparison
  tensor_tmul := e.tensor_tmul
  associator_compat := e.associator_compat
  leftUnitor_compat := e.leftUnitor_compat
  rightUnitor_compat := e.rightUnitor_compat
  power := e.power
  power_zero _ := rfl
  power_one _ := rfl
  power_succ _ _ := rfl
  power_natural := power_natural e

end ScalarExtensionTensorCore

end SheafOfModules
