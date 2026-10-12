/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# Tensor product of sheaves of modules

Source: Stacks Project, Modules on Sites, Section 03EK, Tag 03EK
(blueprint: def-pur-sheaf-tensor-product).

The tensor product `M ⊗ N` of two sheaves of modules over a sheaf of commutative rings `R`
is the source's `SheafOfModules.monoidalCategory R`; the source's
`SheafOfModules.tensorObjIsoSheafification` identifies it with the sheafification
`PresheafOfModules.sheafification (𝟙 _)` of the presheaf tensor product
`PresheafOfModules.Monoidal.tensorObj` of `M.val` and `N.val` (the dependency nodes
`def-weil-presheaf-modules-sheafification` and `def-pur-presheaf-tensor-product`).
The source obtains this monoidal structure for a site `C : Type u`, `Category.{u} C` in the
universe of the rings and modules, so the positive tensor powers are stated there.
This module adds what neither Mathlib nor the source has: the change of rings
`F ⊗_{O₁} O₂` along a morphism of sheaves of rings (for a site in arbitrary universes) and
the positive tensor powers.
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

/-- The sectionwise tensor restriction exists. Source: Stacks, Tag 03EK
(blueprint: def-pur-sheaf-tensor-product).
Proof: send `s ⊗ m` to the tensor of the two restrictions. Additivity and the balanced
relation follow from additivity and semilinearity of restrictions and naturality of `α`.
The tensor universal property gives the map, linear over the source section ring. -/
theorem exists_changeOfRingsMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃ g : (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars (R₂.obj.map f).hom).obj
        ((ModuleCat.extendScalars (α.hom.app Y).hom).obj (M.val.obj Y)),
      ∀ (s : R₂.obj.obj X) (m : M.val.obj X),
        g (s ⊗ₜ[R₁.obj.obj X, (α.hom.app X).hom] m) =
          R₂.obj.map f s ⊗ₜ[R₁.obj.obj Y, (α.hom.app Y).hom] M.val.map f m := by
  sorry

/-- Restriction on the sectionwise change of rings, characterized on pure tensors.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def changeOfRingsMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars (R₂.obj.map f).hom).obj
        ((ModuleCat.extendScalars (α.hom.app Y).hom).obj (M.val.obj Y)) :=
  Classical.choose (exists_changeOfRingsMap α M f)

/-- Identity restriction for change of rings. Source: Stacks, Tag 03EK
(blueprint: def-pur-sheaf-tensor-product).
Proof: the chosen map sends `s ⊗ m` to `s ⊗ m`, since both restrictions are identities.
The identity comparison has the same action; pure tensors generate the tensor product. -/
theorem changeOfRingsMap_id (X : Cᵒᵖ) :
    changeOfRingsMap α M (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((𝓡 R₂).obj.map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((𝓡 R₂).obj.map_id X))).inv.app
          ((ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  convert (Classical.choose_spec (exists_changeOfRingsMap α M (𝟙 X))
    (1 : R₂.obj.obj X) m) using 1 <;>
    simp [changeOfRingsMap, ModuleCat.restrictScalarsId'App_inv_apply]
  · rfl

/-- Composition of restrictions for change of rings. Source: Stacks, Tag 03EK
(blueprint: def-pur-sheaf-tensor-product).
Proof: on `s ⊗ m`, both sides restrict each factor first along `f` and then along `g`.
The ring and module presheaf composition laws identify this with restriction along `f ≫ g`.
The scalar comparison acts identically on elements. Tensor generation gives equality. -/
theorem changeOfRingsMap_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    changeOfRingsMap α M (f ≫ g) = changeOfRingsMap α M f ≫
      (ModuleCat.restrictScalars ((𝓡 R₂).obj.map f).hom).map (changeOfRingsMap α M g) ≫
      (ModuleCat.restrictScalarsComp' ((𝓡 R₂).obj.map f).hom
        ((𝓡 R₂).obj.map g).hom ((𝓡 R₂).obj.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom ((𝓡 R₂).obj.map_comp f g))).inv.app
          ((ModuleCat.extendScalars (α.hom.app Z).hom).obj (M.val.obj Z)) := by
  sorry

/-- Sectionwise change of rings with the induced restrictions, before sheafification.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def changeOfRingsPresheaf : PresheafOfModules.{u} (𝓡 R₂).obj where
  obj X := (ModuleCat.extendScalars (α.hom.app X).hom).obj (M.val.obj X)
  map f := changeOfRingsMap α M f
  map_id X := changeOfRingsMap_id α M X
  map_comp f g := changeOfRingsMap_comp α M f g

/-- Change of rings of a sheaf of modules is the sheafification of sectionwise
extension of scalars, with the target-ring action on the first tensor factor.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def changeOfRings : SheafOfModules.{u} (𝓡 R₂) :=
  (PresheafOfModules.sheafification (𝟙 (𝓡 R₂).obj)).obj (changeOfRingsPresheaf α M)

/-- The sectionwise extension of a module morphism commutes with restrictions.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product).
Proof: on a pure tensor both composites restrict the scalar and apply the original
module morphism to the restricted module section. Naturality of that morphism and
linearity identify the results; pure tensors generate each section tensor product. -/
theorem changeOfRingsHom_naturality {N : SheafOfModules.{u} (𝓡 R₁)} (a : M ⟶ N)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (changeOfRingsPresheaf α M).map i ≫
      (ModuleCat.restrictScalars (R₂.obj.map i).hom).map
        ((ModuleCat.extendScalars (α.hom.app V).hom).map (a.val.app V)) =
    ((ModuleCat.extendScalars (α.hom.app U).hom).map (a.val.app U)) ≫
      (changeOfRingsPresheaf α N).map i := by
  sorry

/-- Change of rings on module morphisms: sheafify the sectionwise map `id ⊗ a`.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
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
of degree `m` with `M` in the source's `SheafOfModules.monoidalCategory R`.
Source: Stacks, Tag 03EK (blueprint: def-pur-sheaf-tensor-product). -/
noncomputable def positiveTensorPower (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (𝓡 R)) : (n : ℕ) → 0 < n → SheafOfModules.{u} (𝓡 R)
  | 0, h => False.elim (Nat.not_lt_zero 0 h)
  | 1, _ => M
  | n + 2, _ =>
    letI := monoidalCategory R
    positiveTensorPower R M (n + 1) (by omega) ⊗ M

end TensorPower

end SheafOfModules
