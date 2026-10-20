/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions
import Sheaf.Paper.ScalarExtensionDualTowerCore
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Tensor powers and duals under scalar extension

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sp-scalar-extension/
  sk-def-sp-scalar-extension-functor.proof.md, proof paragraphs (3) and (4),
  tensor powers and dual evaluation under ordinary scalar extension
(blueprint: lem-sp-invertible-tensor-scalar-extension).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC u m

open CategoryTheory CategoryTheory.Limits
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

/-- Tensor powers and duals commute canonically with scalar extension.
Source: Stacks Project, Tags 03EK, 03EM and 04TT
(blueprint: lem-sp-invertible-tensor-scalar-extension).

Proof: first construct the associators and unitors of the sheaf tensor using the
bilinear universal property. They send `(x ⊗ y) ⊗ z` to `x ⊗ (y ⊗ z)`,
`a ⊗ x` to `a • x`, and `x ⊗ a` to `a • x`; their reverse formulas give inverses.
The scalar-extension unit comparison is multiplication. The tensor comparison sends
`s ⊗ (x ⊗ y)` to `(s ⊗ x) ⊗ (1 ⊗ y)`; its reverse multiplies scalar factors.
The universal property extends the formulas through module sheafification. Define
power comparisons from the unit comparison in degree zero, the identity in degree one,
and recursively from this tensor comparison in higher degrees.
The displayed associator and both unitor squares agree on pure tensors; this proves
compatibility for all parenthesizations of powers, including degrees zero and one.
Naturality follows on the same generators.
For the internal Hom, evaluate `s ⊗ f` on `t ⊗ x` as `st α(f(x))`, with evaluation
on every slice. Trivialize a locally free rank-one module on a covering family; on
each such slice this is multiplication on the unit and is invertible. Glue the
local inverses. The evaluation formula also proves contravariant naturality.
For a tower, send `a ⊗ (s ⊗ x)` to `a β(s) ⊗ x`, with inverse
`a ⊗ x ↦ a ⊗ (1 ⊗ x)`. The power and dual tower squares agree on pure tensors
(and, for the dual, after evaluation). Three ring maps give the same product of
scalar images in the final ring, so this comparison is associative as well.
All constructions use independent site-object, site-morphism and coefficient universes;
the internal Hom is taken in its actual maximum universe. -/
theorem exists_unique_invertibleTensorScalarExtensionData
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [M.IsInvertible] :
    Nonempty (InvertibleTensorScalarExtensionData R S α M) := by
  classical
  obtain ⟨e⟩ := exists_scalarExtensionTensorCore R S α
  let hM : (changeOfRingsOfUniverses α M).IsInvertible :=
    (scalarExtensionDual_localIsomorphism.{uC, vC, u} R S α M).1
  let afterCore (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) :=
    Classical.choice (exists_scalarExtensionTensorCore S T β)
  let compositeCore (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) :=
    Classical.choice (exists_scalarExtensionTensorCore R T (α ≫ β))
  have htower : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (r : ℕ),
      changeOfRingsHomOfUniverses β (changeOfRingsOfUniverses α (scalarTensorPower R M r))
          (e.power M r).hom ≫
          ((afterCore T β).power (changeOfRingsOfUniverses α M) r).hom ≫
          scalarTensorPowerMap T (scalarExtensionTowerIso.{uC, vC, u, u} α β M).hom r =
        (scalarExtensionTowerIso.{uC, vC, u, u} α β (scalarTensorPower R M r)).hom ≫
          ((compositeCore T β).power M r).hom := by
    intro T β r
    induction r using Nat.twoStepInduction with
    | zero => simpa only [ScalarExtensionTensorCore.power, scalarTensorPowerMap,
        scalarTensorPower, Category.comp_id, ScalarExtensionTensorCore.unitComparison]
        using scalarExtensionTowerUnit.{uC, vC, u} α β
    | one => simp only [ScalarExtensionTensorCore.power, scalarTensorPowerMap,
        scalarTensorPower, Iso.refl_hom, scalarExtension_map_id,
        Category.id_comp, Category.comp_id]
    | more r _ ih =>
      simp only [ScalarExtensionTensorCore.power, scalarTensorPowerMap,
        Iso.trans_hom, Functor.mapIso_hom, scalarExtension_map_comp]
      dsimp only [scalarTensorPower]
      simp only [Category.assoc]
      slice_lhs 2 3 =>
        rw [(afterCore T β).first_natural (e.power M (r + 1)).hom
          (changeOfRingsOfUniverses α M)]
      simp only [Category.assoc]
      slice_lhs 3 5 =>
        rw [← Functor.map_comp, ← Functor.map_comp, ih, Functor.map_comp]
      simp only [Category.assoc]
      slice_lhs 4 5 =>
        rw [siteSheafTensorSecondMap_naturality
          ((compositeCore T β).power M (r + 1)).hom
          (scalarExtensionTowerIso.{uC, vC, u, u} α β M).hom]
      slice_lhs 1 4 =>
        rw [scalarExtensionTowerTensor.{uC, vC, u} α β _ _ e (afterCore T β) (compositeCore T β)]
      simp only [Category.assoc]
  refine ⟨{
    toScalarExtensionTensorComparison := e.withPowers
    dual := fun N _ ↦ scalarExtensionDualIso.{uC, vC, u} α N
    dual_tmul := ?_
    dual_natural := ?_
    after := fun T β ↦ (afterCore T β).withPowers
    composite := fun T β ↦ (compositeCore T β).withPowers
    tower := fun _ β N ↦ scalarExtensionTowerIso.{uC, vC, u, u} α β N
    tower_tmul := ?_
    tower_power := htower
    dual_after := fun _ β ↦ scalarExtensionDualIso.{uC, vC, u} β (changeOfRingsOfUniverses α M)
    dual_after_tmul := ?_
    dual_composite := fun _ β ↦ scalarExtensionDualIso.{uC, vC, u} (α ≫ β) M
    dual_composite_tmul := ?_
    dual_tower := fun _ β ↦
      scalarExtensionTowerIso.{uC, vC, u, max uC vC u} α β (homObj M (𝒪 R))
    dual_tower_tmul := ?_
    tower_dual := ?_ }⟩
  · intro N hN
    simpa only [scalarExtensionDualIso_hom] using scalarExtensionDualMap_tmul α N
  · intro N P hN hP f
    simpa only [scalarExtensionDualIso_hom] using scalarExtensionDualMap_natural α N P f
  · simp only [scalarExtensionTowerIso_hom]
    exact fun _ β N ↦ scalarExtensionTowerForward_tmul.{uC, vC, u, u} α β N
  · intro T β
    simpa only [scalarExtensionDualIso_hom] using
      scalarExtensionDualMap_tmul β (changeOfRingsOfUniverses α M)
  · intro T β
    simpa only [scalarExtensionDualIso_hom] using scalarExtensionDualMap_tmul (α ≫ β) M
  · simp only [scalarExtensionTowerIso_hom]
    exact fun _ β ↦
      scalarExtensionTowerForward_tmul.{uC, vC, u, max uC vC u} α β (homObj M (𝒪 R))
  · intro T β
    simpa only [scalarExtensionDualIso_hom] using scalarExtensionTowerDual α β M

end SheafOfModules
