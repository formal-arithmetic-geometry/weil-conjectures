/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# Tensor product of sheaves of modules

The tensor product `M ⊗ N` of two sheaves of modules over a sheaf of commutative rings `R`
is given by `SheafOfModules.monoidalCategory R`; `SheafOfModules.tensorObjIsoSheafification`
identifies it with the sheafification `PresheafOfModules.sheafification (𝟙 _)` of the presheaf
tensor product `PresheafOfModules.Monoidal.tensorObj` of `M.val` and `N.val`. This monoidal
structure is available for a site `C : Type u`, `Category.{u} C` in the universe of the rings and
modules, so the positive tensor powers are stated there. This file adds the change of rings
`F ⊗_{O₁} O₂` along a morphism of sheaves of rings (for a site in arbitrary universes) and
the positive tensor powers.

## References

* Stacks Project, Modules on Sites, Section 03EK
-/

@[expose] public section

universe v₀ u₀ u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

section ChangeOfRings

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

open scoped ChangeOfRings

variable {R₁ R₂ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂)
  (M : SheafOfModules.{u} (𝓡 R₁))

local instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Module (R₁.obj.obj Y)
      ((ModuleCat.restrictScalars ((𝓡 R₁).obj.map f).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (R₁.obj.obj Y) (M.val.obj Y))

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise tensor restriction exists. -/
theorem exists_changeOfRingsMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃ g : (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars (R₂.obj.map f).hom).obj
        ((ModuleCat.extendScalars (α.hom.app Y).hom).obj (M.val.obj Y)),
      ∀ (s : R₂.obj.obj X) (m : M.val.obj X),
        g (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m) =
          R₂.obj.map f s ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom] M.val.map f m := by
  -- Retain the instance parameters of the original declaration.
  have := ‹J.WEqualsLocallyBijective AddCommGrpCat.{u}›
  have := ‹HasWeakSheafify J AddCommGrpCat.{u}›
  let : Module (R₁.obj.obj Y) (R₂.obj.obj Y) :=
    Module.compHom (R₂.obj.obj Y) (α.hom.app Y).hom
  let T := (ModuleCat.restrictScalars (R₂.obj.map f).hom).obj
    ((ModuleCat.extendScalars (α.hom.app Y).hom).obj (M.val.obj Y))
  let h : M.val.obj X ⟶ (ModuleCat.restrictScalars (α.hom.app X).hom).obj T :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (α.hom.app X).hom).obj T)
      { toFun := fun m ↦ (1 : R₂.obj.obj Y) ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom]
          M.val.map f m
        map_add' := by
          intro m n
          simp [TensorProduct.tmul_add]
        map_smul' := by
          intro r m
          change (1 : R₂.obj.obj Y) ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom]
            M.val.map f (r • m) =
            R₂.obj.map f (α.hom.app X r) •
              ((1 : R₂.obj.obj Y) ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom] M.val.map f m)
          rw [M.val.map_smul]
          have hn : R₂.obj.map f (α.hom.app X r) =
              α.hom.app Y (R₁.obj.map f r) :=
            ConcreteCategory.congr_hom (α.hom.naturality f).symm r
          rw [hn]
          change (1 : R₂.obj.obj Y) ⊗ₜ[R₁.obj.obj Y]
            ((R₁.obj.map f r) • (show M.val.obj Y from M.val.map f m)) = _
          rw [TensorProduct.tmul_smul]
          rfl }
  refine ⟨ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (α.hom.app X).hom h, ?_⟩
  intro s m
  let : Module (R₁.obj.obj X) T := Module.compHom T (α.hom.app X).hom
  let : Module (R₁.obj.obj X) (R₂.obj.obj X) :=
    Module.compHom (R₂.obj.obj X) (α.hom.app X).hom
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change R₂.obj.map f s •
    ((1 : R₂.obj.obj Y) ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom] M.val.map f m) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

/-- Restriction on the sectionwise change of rings, characterized on pure tensors. -/
noncomputable def changeOfRingsMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars (R₂.obj.map f).hom).obj
        ((ModuleCat.extendScalars (α.hom.app Y).hom).obj (M.val.obj Y)) :=
  Classical.choose (exists_changeOfRingsMap α M f)

private theorem changeOfRingsMap_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : R₂.obj.obj X) (m : M.val.obj X) :
    changeOfRingsMap α M f (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m) =
      R₂.obj.map f s ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom] M.val.map f m :=
  Classical.choose_spec (exists_changeOfRingsMap α M f) s m

set_option backward.isDefEq.respectTransparency false in
/-- Identity restriction for change of rings. -/
theorem changeOfRingsMap_id (X : Cᵒᵖ) :
    changeOfRingsMap α M (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((𝓡 R₂).obj.map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((𝓡 R₂).obj.map_id X))).inv.app
          ((ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  rw [changeOfRingsMap_tmul]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composition of restrictions for change of rings. -/
theorem changeOfRingsMap_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    changeOfRingsMap α M (f ≫ g) = changeOfRingsMap α M f ≫
      (ModuleCat.restrictScalars ((𝓡 R₂).obj.map f).hom).map (changeOfRingsMap α M g) ≫
      (ModuleCat.restrictScalarsComp' ((𝓡 R₂).obj.map f).hom
        ((𝓡 R₂).obj.map g).hom ((𝓡 R₂).obj.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom ((𝓡 R₂).obj.map_comp f g))).inv.app
          ((ModuleCat.extendScalars (α.hom.app Z).hom).obj (M.val.obj Z)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  simp only [ModuleCat.comp_apply, changeOfRingsMap_tmul]
  change _ = changeOfRingsMap α M g _
  rw [changeOfRingsMap_tmul]
  simp

/-- Sectionwise change of rings with the induced restrictions, before sheafification. -/
noncomputable def changeOfRingsPresheaf : PresheafOfModules.{u} (𝓡 R₂).obj where
  obj X := (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X)
  map f := changeOfRingsMap α M f
  map_id X := changeOfRingsMap_id α M X
  map_comp f g := changeOfRingsMap_comp α M f g

/-- Change of rings of a sheaf of modules is the sheafification of sectionwise
extension of scalars, with the target-ring action on the first tensor factor. -/
noncomputable def changeOfRings : SheafOfModules.{u} (𝓡 R₂) :=
  (PresheafOfModules.sheafification (𝟙 (𝓡 R₂).obj)).obj (changeOfRingsPresheaf α M)

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise extension of a module morphism commutes with restrictions. -/
theorem changeOfRingsHom_naturality {N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (changeOfRingsPresheaf α M).map i ≫
      (ModuleCat.restrictScalars (R₂.obj.map i).hom).map
        ((ModuleCat.extendScalars (α.hom.app V).hom).map (a.val.app V)) =
    ((ModuleCat.extendScalars (α.hom.app U).hom).map (a.val.app U)) ≫
      (changeOfRingsPresheaf α N).map i := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (ModuleCat.extendScalars (α.hom.app V).hom).map (a.val.app V)
    (changeOfRingsMap α M i _) = changeOfRingsMap α N i
      ((ModuleCat.extendScalars (α.hom.app U).hom).map (a.val.app U) _)
  rw [changeOfRingsMap_tmul]
  erw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.map_tmul]
  rw [changeOfRingsMap_tmul]
  congr 1
  exact PresheafOfModules.naturality_apply a.val i m

/-- Change of rings on module morphisms: sheafify the sectionwise map `id ⊗ a`. -/
noncomputable def changeOfRingsHom {N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N) :
    changeOfRings α M ⟶ changeOfRings α N :=
  (PresheafOfModules.sheafification (𝟙 (𝓡 R₂).obj)).map
    { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (a.val.app U)
      naturality := changeOfRingsHom_naturality α M a }

end ChangeOfRings

section TensorPower

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Positive tensor powers: degree one is `M`, and degree `m + 1` is the tensor product
of degree `m` with `M` in `SheafOfModules.monoidalCategory R`. -/
noncomputable def positiveTensorPower (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (𝓡 R)) : (n : ℕ) → 0 < n → SheafOfModules.{u} (𝓡 R)
  | 0, h => False.elim (Nat.not_lt_zero 0 h)
  | 1, _ => M
  | n + 2, _ =>
    letI := monoidalCategory R
    positiveTensorPower R M (n + 1) (by omega) ⊗ M

end TensorPower

end SheafOfModules
