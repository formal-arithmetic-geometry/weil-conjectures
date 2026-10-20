/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.ScalarExtensionDualLocalIso

/-!
# Duals and binary ring towers under scalar extension

Source: Stacks Project, Tags 03EK, 03EM, 04TT.
(blueprint: lem-sp-scalar-extension-dual-tower-core).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
-- Universe-polymorphic sheafification instances make the section-variable linter expensive.
set_option linter.unusedSectionVars false

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

attribute [local irreducible] scalarExtensionLift
  scalarExtensionDualMap scalarExtensionUnitIso changeOfRingsHomOfUniverses

section Universes

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
  [HasWeakSheafify J AddCommGrpCat.{max u m}]

/-- scalarExtensionEmbedding: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionEmbedding {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      (changeOfRingsOfUniverses α N) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom (Y :=
        (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
          (changeOfRingsOfUniverses α N)).val.obj U))
        { toFun := fun x ↦ scalarExtensionSection α N U 1 x
          map_add' := scalarExtensionSection_add α N U 1
          map_smul' := by
            intro a x
            change scalarExtensionSection α N U 1 (a • x) =
              α.hom.app U a • scalarExtensionSection α N U 1 x
            erw [scalarExtensionSection_base_smul, one_mul,
              scalarExtensionSection_smul, mul_one] }
      naturality := by
        intro U V i
        ext x
        change scalarExtensionSection α N V 1 (N.val.map i x) =
          (changeOfRingsOfUniverses α N).val.map i (scalarExtensionSection α N U 1 x)
        erw [scalarExtensionSection_naturality, map_one] }

/-- scalarExtensionTowerMiddle: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerMiddle {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses α N ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map β)).obj
        (changeOfRingsOfUniverses (α ≫ β) N) :=
  scalarExtensionLift α N _
    { val :=
        { app := fun U ↦ ModuleCat.ofHom (Y :=
            (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
              ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map β)).obj
                (changeOfRingsOfUniverses (α ≫ β) N))).val.obj U))
            { toFun := fun x ↦ scalarExtensionSection (α ≫ β) N U 1 x
              map_add' := scalarExtensionSection_add (α ≫ β) N U 1
              map_smul' := by
                intro a x
                change scalarExtensionSection (α ≫ β) N U 1 (a • x) =
                  β.hom.app U (α.hom.app U a) •
                    scalarExtensionSection (α ≫ β) N U 1 x
                erw [scalarExtensionSection_base_smul, one_mul,
                  scalarExtensionSection_smul, mul_one]
                rfl }
          naturality := by
            intro U V i
            ext x
            change scalarExtensionSection (α ≫ β) N V 1 (N.val.map i x) =
              (changeOfRingsOfUniverses (α ≫ β) N).val.map i
                (scalarExtensionSection (α ≫ β) N U 1 x)
            erw [scalarExtensionSection_naturality, map_one] } }

/-- scalarExtensionTowerForward: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerForward {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) ⟶
      changeOfRingsOfUniverses (α ≫ β) N :=
  scalarExtensionLift β (changeOfRingsOfUniverses α N) _
    (scalarExtensionTowerMiddle α β N)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTowerForward_tmul: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTowerForward_tmul {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (a : T.obj.obj U) (s : S.obj.obj U) (x : N.val.obj U) :
    (scalarExtensionTowerForward α β N).val.app U
      (scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
        (scalarExtensionSection α N U s x)) =
      scalarExtensionSection (α ≫ β) N U (a * β.hom.app U s) x := by
  rw [scalarExtensionTowerForward, scalarExtensionLift_tmul]
  unfold scalarExtensionTowerMiddle
  rw [scalarExtensionLift_tmul]
  change a • (β.hom.app U s • scalarExtensionSection (α ≫ β) N U 1 x) = _
  rw [scalarExtensionSection_smul, mul_one, scalarExtensionSection_smul]

/-- scalarExtensionTowerBaseReverse: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerBaseReverse {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    N ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map (α ≫ β))).obj
      (changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N)) :=
  scalarExtensionEmbedding α N ≫
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).map
      (scalarExtensionEmbedding β (changeOfRingsOfUniverses α N))

/-- scalarExtensionTowerReverse: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerReverse {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses (α ≫ β) N ⟶
      changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) :=
  scalarExtensionLift (α ≫ β) N _ (scalarExtensionTowerBaseReverse α β N)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTowerReverse_tmul: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTowerReverse_tmul {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (a : T.obj.obj U) (x : N.val.obj U) :
    (scalarExtensionTowerReverse α β N).val.app U
      (scalarExtensionSection (α ≫ β) N U a x) =
      scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
        (scalarExtensionSection α N U 1 x) := by
  rw [scalarExtensionTowerReverse, scalarExtensionLift_tmul]
  unfold scalarExtensionTowerBaseReverse scalarExtensionEmbedding
  change a • scalarExtensionSection β (changeOfRingsOfUniverses α N) U 1
    (scalarExtensionSection α N U 1 x) = _
  rw [scalarExtensionSection_smul, mul_one]


omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTower_hom_ext: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTower_hom_ext {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) {H : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj T)}
    (f g : changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) ⟶ H)
    (h : ∀ U a s x, f.val.app U
      (scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
        (scalarExtensionSection α N U s x)) =
      g.val.app U (scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
        (scalarExtensionSection α N U s x))) : f = g := by
  apply scalarExtension_hom_ext β (changeOfRingsOfUniverses α N)
  intro U a z
  let η := scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (changeOfRingsOfUniverses α N).val.map i.op z at ht
  change H.val.map i.op (f.val.app U _) = H.val.map i.op (g.val.app U _)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val, scalarExtensionSection_naturality, ← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [(η.app (op V)).hom.map_zero, scalarExtensionSection_zero,
      (f.val.app (op V)).hom.map_zero, (g.val.app (op V)).hom.map_zero]
  | add t t' ih ih' =>
    erw [(η.app (op V)).hom.map_add, scalarExtensionSection_add,
      (f.val.app (op V)).hom.map_add, (g.val.app (op V)).hom.map_add, ih, ih']
  | tmul s x =>
    simpa only [η, scalarSheafificationUnit, scalarExtensionSection] using!
      h (op V) (T.obj.map i.op a) s x

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTower_reverse_forward: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTower_reverse_forward {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    scalarExtensionTowerReverse α β N ≫ scalarExtensionTowerForward α β N = 𝟙 _ := by
  apply scalarExtension_hom_ext (α ≫ β) N
  intro U a x
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtensionTowerReverse_tmul, scalarExtensionTowerForward_tmul, map_one, mul_one,
    id_val, PresheafOfModules.id_app, ModuleCat.id_apply]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- scalarExtensionTower_forward_reverse: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTower_forward_reverse {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    scalarExtensionTowerForward α β N ≫ scalarExtensionTowerReverse α β N = 𝟙 _ := by
  apply scalarExtensionTower_hom_ext α β N
  intro U a s x
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtensionTowerForward_tmul, scalarExtensionTowerReverse_tmul,
    id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  have hs := scalarExtensionSection_smul α N U s 1 x
  rw [mul_one] at hs
  rw [← hs, scalarExtensionSection_base_smul]

/-- scalarExtensionTowerIso: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
noncomputable def scalarExtensionTowerIso {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) ≅
      changeOfRingsOfUniverses (α ≫ β) N where
  hom := scalarExtensionTowerForward α β N
  inv := scalarExtensionTowerReverse α β N
  hom_inv_id := scalarExtensionTower_forward_reverse α β N
  inv_hom_id := scalarExtensionTower_reverse_forward α β N


/-- The tower comparison has the explicitly constructed forward component.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-scalar-extension-dual-tower-core). -/
theorem scalarExtensionTowerIso_hom {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : SheafOfModules.{max u m} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) :
    (scalarExtensionTowerIso α β N).hom = scalarExtensionTowerForward α β N := rfl

attribute [irreducible] scalarExtensionTowerIso

end Universes

/-- scalarExtensionTowerUnit: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTowerUnit {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) :
    changeOfRingsHomOfUniverses β (changeOfRingsOfUniverses α (𝒪 R))
      (scalarExtensionUnitIso α).hom ≫ (scalarExtensionUnitIso β).hom =
      (scalarExtensionTowerIso α β (𝒪 R)).hom ≫ (scalarExtensionUnitIso (α ≫ β)).hom := by
  apply scalarExtensionTower_hom_ext α β (𝒪 R)
  intro U a s x
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtension_map_tmul, scalarExtensionUnitIso_tmul,
    scalarExtensionTowerIso_hom, scalarExtensionTowerForward_tmul]
  change a * β.hom.app U (s * α.hom.app U x) =
    (a * β.hom.app U s) * β.hom.app U (α.hom.app U x)
  rw [map_mul, mul_assoc]

/-- scalarExtensionTowerTensor: scalar-extension ring-tower construction.
Source: Stacks, Tag 03EK (blueprint: lem-sp-scalar-extension-dual-tower-core).
The maps multiply the two scalar factors; tensor generation and the sheafification
adjunction prove the formulas and equality of the two normalized composites. -/
theorem scalarExtensionTowerTensor {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N P : Mod R)
    (e : ScalarExtensionTensorCore R S α) (f : ScalarExtensionTensorCore S T β)
    (g : ScalarExtensionTensorCore R T (α ≫ β)) :
    changeOfRingsHomOfUniverses β (changeOfRingsOfUniverses α (𝒯 N P))
      (e.tensorComparison N P).hom ≫
      (f.tensorComparison (changeOfRingsOfUniverses α N)
        (changeOfRingsOfUniverses α P)).hom ≫
      (siteSheafTensorRight
        (changeOfRingsOfUniverses β (changeOfRingsOfUniverses α P))).map
          (scalarExtensionTowerIso α β N).hom ≫
      siteSheafTensorSecondMap (changeOfRingsOfUniverses (α ≫ β) N)
        (scalarExtensionTowerIso α β P).hom =
      (scalarExtensionTowerIso α β (𝒯 N P)).hom ≫ (g.tensorComparison N P).hom := by
  let l := changeOfRingsHomOfUniverses β (changeOfRingsOfUniverses α (𝒯 N P))
      (e.tensorComparison N P).hom ≫
      (f.tensorComparison (changeOfRingsOfUniverses α N)
        (changeOfRingsOfUniverses α P)).hom ≫
      (siteSheafTensorRight
        (changeOfRingsOfUniverses β (changeOfRingsOfUniverses α P))).map
          (scalarExtensionTowerIso α β N).hom ≫
      siteSheafTensorSecondMap (changeOfRingsOfUniverses (α ≫ β) N)
        (scalarExtensionTowerIso α β P).hom
  let r := (scalarExtensionTowerIso α β (𝒯 N P)).hom ≫ (g.tensorComparison N P).hom
  change l = r
  apply scalarExtensionTower_hom_ext α β (𝒯 N P)
  intro U a s z
  let η := scalarSheafificationUnit (siteTensorPresheaf N.val P.val)
  let H := (siteSheafTensorRight (changeOfRingsOfUniverses (α ≫ β) P)).obj
    (changeOfRingsOfUniverses (α ≫ β) N)
  apply H.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (𝒯 N P).val.map i.op z at ht
  change H.val.map i.op (l.val.app U _) = H.val.map i.op (r.val.app U _)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply,
    scalarExtensionSection_naturality, scalarExtensionSection_naturality, ← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [(η.app (op V)).hom.map_zero, scalarExtensionSection_zero, scalarExtensionSection_zero,
      (l.val.app (op V)).hom.map_zero, (r.val.app (op V)).hom.map_zero]
  | add t t' ht ht' =>
    erw [(η.app (op V)).hom.map_add, scalarExtensionSection_add, scalarExtensionSection_add,
      (l.val.app (op V)).hom.map_add, (r.val.app (op V)).hom.map_add, ht, ht']
  | tmul x y =>
    change l.val.app (op V)
      (scalarExtensionSection β (changeOfRingsOfUniverses α (𝒯 N P)) (op V)
        (T.obj.map i.op a) (scalarExtensionSection α (𝒯 N P) (op V)
          (S.obj.map i.op s) (siteSheafTensorTmul N P (op V) x y))) =
      r.val.app (op V)
      (scalarExtensionSection β (changeOfRingsOfUniverses α (𝒯 N P)) (op V)
        (T.obj.map i.op a) (scalarExtensionSection α (𝒯 N P) (op V)
          (S.obj.map i.op s) (siteSheafTensorTmul N P (op V) x y)))
    dsimp only [l, r]
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      scalarExtension_map_tmul, e.tensor_tmul, f.tensor_tmul,
      scalarTensor_first_tmul, scalarTensor_second_tmul,
      scalarExtensionTowerIso_hom, scalarExtensionTowerForward_tmul,
      g.tensor_tmul, map_one, mul_one]


omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- Evaluation at identity slices detects maps into an internal dual.
Source: Stacks, Tag 04TT (blueprint: lem-sp-scalar-extension-dual-tower-core).
Naturality moves every slice component to its identity object. -/
theorem scalarDual_hom_ext {R : Sheaf J CommRingCat.{u}} (N : Mod R)
    {H : SheafOfModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f g : H ⟶ homObj N (𝒪 R))
    (h : ∀ (U : Cᵒᵖ) (z : H.val.obj U) (x : N.val.obj U),
      (f.val.app U z).app (op (Over.mk (𝟙 U.unop))) x =
        (g.val.app U z).app (op (Over.mk (𝟙 U.unop))) x) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh := h (op W.unop.left) (H.val.map W.unop.hom.op z) x
  rw [PresheafOfModules.naturality_apply f.val,
    PresheafOfModules.naturality_apply g.val] at hh
  change (f.val.app U z).app (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom))) x =
    (g.val.app U z).app (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom))) x at hh
  exact (PresheafOfModules.restrictOver_hom_app_congr (f.val.app U z)
    (Category.id_comp W.unop.hom) x).symm.trans
      (hh.trans (PresheafOfModules.restrictOver_hom_app_congr (g.val.app U z)
        (Category.id_comp W.unop.hom) x))


/-- Nested scalar-extension tensors detect sections of the internal dual of a tower.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-tower-core).
Proof: descend through the outer scalar extension, then through the locally bijective
unit of the inner scalar extension. Additivity reduces tensor sums to generators. -/
theorem scalarDualTower_section_ext {R S T : Sheaf J CommRingCat.{u}}
    (α : R ⟶ S) (β : S ⟶ T) (N : Mod R) (U : Cᵒᵖ)
    (φ ψ : (homObj (changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N))
      (𝒪 T)).val.obj U)
    (h : ∀ (W : (Over U.unop)ᵒᵖ) (a : T.obj.obj (op W.unop.left))
      (s : S.obj.obj (op W.unop.left)) (x : N.val.obj (op W.unop.left)),
      φ.app W (scalarExtensionSection β (changeOfRingsOfUniverses α N)
        (op W.unop.left) a (scalarExtensionSection α N (op W.unop.left) s x)) =
      ψ.app W (scalarExtensionSection β (changeOfRingsOfUniverses α N)
        (op W.unop.left) a (scalarExtensionSection α N (op W.unop.left) s x))) :
    φ = ψ := by
  apply scalarDual_section_ext β (changeOfRingsOfUniverses α N) U
  intro W a z
  let η := scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)
  apply (𝒪 T).isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (changeOfRingsOfUniverses α N).val.map i.op z at ht
  let k : Over.mk (i ≫ W.unop.hom) ⟶ W.unop := Over.homMk i
  have hp := PresheafOfModules.naturality_apply φ k.op
    (scalarExtensionSection β (changeOfRingsOfUniverses α N) _ a z)
  have hq := PresheafOfModules.naturality_apply ψ k.op
    (scalarExtensionSection β (changeOfRingsOfUniverses α N) _ a z)
  change (𝒪 T).val.map i.op (φ.app W _) = (𝒪 T).val.map i.op (ψ.app W _)
  refine hp.symm.trans (Eq.trans ?_ hq)
  change φ.app (op (Over.mk (i ≫ W.unop.hom)))
      ((changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N)).val.map i.op
        (scalarExtensionSection β (changeOfRingsOfUniverses α N) _ a z)) =
    ψ.app (op (Over.mk (i ≫ W.unop.hom)))
      ((changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N)).val.map i.op
        (scalarExtensionSection β (changeOfRingsOfUniverses α N) _ a z))
  rw [scalarExtensionSection_naturality, ← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [(η.app (op V)).hom.map_zero, scalarExtensionSection_zero,
      (φ.app (op (Over.mk (i ≫ W.unop.hom)))).hom.map_zero,
      (ψ.app (op (Over.mk (i ≫ W.unop.hom)))).hom.map_zero]
  | add t t' ht ht' =>
    erw [(η.app (op V)).hom.map_add, scalarExtensionSection_add,
      (φ.app (op (Over.mk (i ≫ W.unop.hom)))).hom.map_add,
      (ψ.app (op (Over.mk (i ≫ W.unop.hom)))).hom.map_add, ht, ht']
  | tmul s x =>
    simpa only [η, scalarSheafificationUnit, scalarExtensionSection,
      Over.mk_left, unop_op] using!
      h (op (Over.mk (i ≫ W.unop.hom))) (T.obj.map i.op a) s x

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] changeOfRingsOfUniverses scalarExtensionSection
  siteSheafTensorTmul siteSheafTensorRight siteSheafTensorSecondMap

/-- The explicit dual map as an isomorphism, using its proved local inverses.
Source: Stacks Project, Tags 03EM and 04TT
(blueprint: lem-sp-scalar-extension-dual-tower-core). -/
noncomputable def scalarExtensionDualIso
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) (N : Mod R)
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [N.IsInvertible] : changeOfRingsOfUniverses α (homObj N (𝒪 R)) ≅
      homObj (changeOfRingsOfUniverses α N) (𝒪 S) :=
  @asIso _ _ _ _ (scalarExtensionDualMap α N)
    (scalarExtensionDual_localIsomorphism R S α N).2

/-- The forward dual comparison is the evaluation map.
Source: Stacks Project, Tag 04TT
(blueprint: lem-sp-scalar-extension-dual-tower-core). -/
theorem scalarExtensionDualIso_hom
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) (N : Mod R)
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [N.IsInvertible] :
    (scalarExtensionDualIso.{uC, vC, u} α N).hom = scalarExtensionDualMap α N := rfl

attribute [local irreducible] scalarExtensionDualIso

attribute [local irreducible] scalarExtensionTowerForward scalarExtensionTowerReverse

/-- The explicit scalar-extension dual evaluation commutes with a ring tower.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-tower-core).
Proof: test maps on nested scalar-extension generators and evaluate the resulting
functionals on every slice. Naturality of the ring map and associativity and
commutativity of multiplication identify the two scalar products. -/
theorem scalarExtensionTowerDual
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R S T : Sheaf J CommRingCat.{u}} (α : R ⟶ S) (β : S ⟶ T) (M : Mod R) :
    changeOfRingsHomOfUniverses β _ (scalarExtensionDualMap α M) ≫
        scalarExtensionDualMap β (changeOfRingsOfUniverses α M) =
      (scalarExtensionTowerIso.{uC, vC, u, max uC vC u} α β (homObj M (𝒪 R))).hom ≫
        scalarExtensionDualMap (α ≫ β) M ≫
          homObjMap (scalarExtensionTowerIso.{uC, vC, u, u} α β M).hom (𝟙 (𝒪 T)) := by
  apply scalarExtensionTower_hom_ext.{uC, vC, u, max uC vC u} α β (homObj M (𝒪 R))
  intro U a s φ
  apply scalarDualTower_section_ext α β M U
  intro W b t x
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarExtension_map_tmul, scalarExtensionDualMap_tmul_slice,
    scalarExtensionTowerIso_hom, scalarExtensionTowerForward_tmul]
  change (T.obj.map W.unop.hom.op a * b * β.hom.app (op W.unop.left)
      (S.obj.map W.unop.hom.op s * t *
        α.hom.app (op W.unop.left) (φ.app W x))) =
    (((scalarExtensionDualMap (α ≫ β) M).val.app U
      (scalarExtensionSection (α ≫ β) (homObj M (𝒪 R)) U
        (a * β.hom.app U s) φ)).app W)
      ((scalarExtensionTowerForward.{uC, vC, u, u} α β M).val.app (op W.unop.left)
        (scalarExtensionSection β (changeOfRingsOfUniverses α M) (op W.unop.left) b
          (scalarExtensionSection α M (op W.unop.left) t x)))
  rw [scalarExtensionTowerForward_tmul, scalarExtensionDualMap_tmul_slice]
  change _ = T.obj.map W.unop.hom.op (a * β.hom.app U s) *
    (b * β.hom.app (op W.unop.left) t) *
      β.hom.app (op W.unop.left) (α.hom.app (op W.unop.left) (φ.app W x))
  rw [map_mul, map_mul, map_mul]
  have hβ := ConcreteCategory.congr_hom (β.hom.naturality W.unop.hom.op) s
  change β.hom.app (op W.unop.left) (S.obj.map W.unop.hom.op s) =
    T.obj.map W.unop.hom.op (β.hom.app U s) at hβ
  rw [hβ]
  ac_rfl

end SheafOfModules
