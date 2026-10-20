/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Tensor powers and duals under scalar extension

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sp-scalar-extension/
  sk-def-sp-scalar-extension-functor.proof.md, proof paragraphs (3) and (4),
  tensor powers and dual evaluation under ordinary scalar extension
(blueprint: lem-sp-invertible-tensor-scalar-extension).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

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

/-- The tensor power with the unit in degree zero.
Source: Stacks Project, Tag 03EK (blueprint: lem-sp-invertible-tensor-scalar-extension).
Positive powers are left associated, with degree one equal to `M` as in the dependency. -/
noncomputable def scalarTensorPower (R : Sheaf J CommRingCat.{u}) (M : Mod R) : ℕ → Mod R
  | 0 => 𝒪 R
  | 1 => M
  | n + 2 => 𝒯 (scalarTensorPower R M (n + 1)) M

/-- The map on tensor powers induced by a module morphism.
Source: Stacks Project, Tag 03EK (blueprint: lem-sp-invertible-tensor-scalar-extension). -/
noncomputable def scalarTensorPowerMap
    (R : Sheaf J CommRingCat.{u}) {M N : Mod R} (f : M ⟶ N) :
    ∀ r : ℕ, scalarTensorPower R M r ⟶ scalarTensorPower R N r
  | 0 => 𝟙 _
  | 1 => f
  | n + 2 =>
      (siteSheafTensorRight M).map (scalarTensorPowerMap R f (n + 1)) ≫
        siteSheafTensorSecondMap (scalarTensorPower R N (n + 1)) f

/-- The image of a pure scalar-extension tensor under the module sheafification unit.
The module universe may exceed the coefficient universe, as happens for internal Hom.
Source: Stacks, Tag 03EK (blueprint: lem-sp-invertible-tensor-scalar-extension). -/
noncomputable def scalarExtensionSection
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u m}]
    [HasWeakSheafify J AddCommGrpCat.{max u m}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRingsOfUniverses α M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
      (changeOfRingsPresheafOfUniverses α M)).app U)
        (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection
  siteSheafTensorTmul siteSheafTensorRight siteSheafTensorSecondMap

/-- Canonical associators and unitors for the actual sheafified tensor product.
Each isomorphism is specified by its action on local pure tensors, rather than an
unspecified monoidal structure. Source: Stacks, Tag 03EK
(blueprint: lem-sp-invertible-tensor-scalar-extension). -/
structure ScalarTensorCoherence (R : Sheaf J CommRingCat.{u}) where
  associator : ∀ (N P Q : Mod R), 𝒯 (𝒯 N P) Q ≅ 𝒯 N (𝒯 P Q)
  associator_tmul : ∀ (N P Q : Mod R) (U : Cᵒᵖ)
      (x : N.val.obj U) (y : P.val.obj U) (z : Q.val.obj U),
    ((associator N P Q).hom.val.app U)
        (siteSheafTensorTmul (𝒯 N P) Q U (siteSheafTensorTmul N P U x y) z) =
      siteSheafTensorTmul N (𝒯 P Q) U x (siteSheafTensorTmul P Q U y z)
  leftUnitor : ∀ N : Mod R, 𝒯 (𝒪 R) N ≅ N
  leftUnitor_tmul : ∀ (N : Mod R) (U : Cᵒᵖ) (a : R.obj.obj U) (x : N.val.obj U),
    ((leftUnitor N).hom.val.app U) (siteSheafTensorTmul (𝒪 R) N U a x) = a • x
  rightUnitor : ∀ N : Mod R, 𝒯 N (𝒪 R) ≅ N
  rightUnitor_tmul : ∀ (N : Mod R) (U : Cᵒᵖ) (x : N.val.obj U) (a : R.obj.obj U),
    ((rightUnitor N).hom.val.app U) (siteSheafTensorTmul N (𝒪 R) U x a) = a • x

/-- Scalar-extension tensor comparisons, with explicit associator and unitor squares.
The pure-tensor normalizations determine the comparisons and hence their canonicity.
Source: Stacks, Tag 03EK (blueprint: lem-sp-invertible-tensor-scalar-extension). -/
structure ScalarExtensionTensorComparison
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) where
  sourceCoherence : ScalarTensorCoherence R
  targetCoherence : ScalarTensorCoherence S
  unitComparison : changeOfRingsOfUniverses α (𝒪 R) ≅ 𝒪 S
  unit_tmul : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (a : R.obj.obj U),
    (unitComparison.hom.val.app U) (scalarExtensionSection α (𝒪 R) U s a) =
      s * α.hom.app U a
  tensorComparison : ∀ (N P : Mod R),
    changeOfRingsOfUniverses α (𝒯 N P) ≅
      𝒯 (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P)
  tensor_tmul : ∀ (N P : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U)
      (x : N.val.obj U) (y : P.val.obj U),
    ((tensorComparison N P).hom.val.app U)
        (scalarExtensionSection α (𝒯 N P) U s (siteSheafTensorTmul N P U x y)) =
      siteSheafTensorTmul (changeOfRingsOfUniverses α N) (changeOfRingsOfUniverses α P) U
        (scalarExtensionSection α N U s x) (scalarExtensionSection α P U 1 y)
  associator_compat : ∀ (N P Q : Mod R),
    changeOfRingsHomOfUniverses α _ (sourceCoherence.associator N P Q).hom ≫
        (tensorComparison N (𝒯 P Q)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N)
          (tensorComparison P Q).hom =
      (tensorComparison (𝒯 N P) Q).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α Q)).map
          (tensorComparison N P).hom ≫
        (targetCoherence.associator (changeOfRingsOfUniverses α N)
          (changeOfRingsOfUniverses α P) (changeOfRingsOfUniverses α Q)).hom
  leftUnitor_compat : ∀ (N : Mod R),
    (tensorComparison (𝒪 R) N).hom ≫
        (siteSheafTensorRight (changeOfRingsOfUniverses α N)).map unitComparison.hom ≫
        (targetCoherence.leftUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ (sourceCoherence.leftUnitor N).hom
  rightUnitor_compat : ∀ (N : Mod R),
    (tensorComparison N (𝒪 R)).hom ≫
        siteSheafTensorSecondMap (changeOfRingsOfUniverses α N) unitComparison.hom ≫
        (targetCoherence.rightUnitor (changeOfRingsOfUniverses α N)).hom =
      changeOfRingsHomOfUniverses α _ (sourceCoherence.rightUnitor N).hom
  power : ∀ (N : Mod R) (r : ℕ),
    changeOfRingsOfUniverses α (scalarTensorPower R N r) ≅
      scalarTensorPower S (changeOfRingsOfUniverses α N) r
  power_zero : ∀ N : Mod R, (power N 0).hom = unitComparison.hom
  power_one : ∀ N : Mod R, (power N 1).hom = 𝟙 _
  power_succ : ∀ (N : Mod R) (r : ℕ),
    (power N (r + 2)).hom = (tensorComparison (scalarTensorPower R N (r + 1)) N).hom ≫
      (siteSheafTensorRight (changeOfRingsOfUniverses α N)).map (power N (r + 1)).hom
  power_natural : ∀ (N P : Mod R) (f : N ⟶ P) (r : ℕ),
    changeOfRingsHomOfUniverses α _ (scalarTensorPowerMap R f r) ≫ (power P r).hom =
      (power N r).hom ≫ scalarTensorPowerMap S (changeOfRingsHomOfUniverses α N f) r

/-- The scalar-extension comparisons for tensor powers and internal duals, including
commuting diagrams for iterated ring maps. The larger sheafification universe is the
one required by the recorded internal Hom, with no equality of site universes imposed.
Source: Stacks, Tags 03EK, 03EM and 04TT
(blueprint: lem-sp-invertible-tensor-scalar-extension). -/
structure InvertibleTensorScalarExtensionData
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    (R S : Sheaf J CommRingCat.{u}) (α : R ⟶ S) (M : Mod R)
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [M.IsInvertible] extends ScalarExtensionTensorComparison R S α where
  dual : ∀ (N : Mod R) [N.IsInvertible],
    changeOfRingsOfUniverses α (homObj N (𝒪 R)) ≅
      homObj (changeOfRingsOfUniverses α N) (𝒪 S)
  dual_tmul : ∀ (N : Mod R) [N.IsInvertible] (U : Cᵒᵖ)
      (s t : S.obj.obj U) (f : (homObj N (𝒪 R)).val.obj U) (x : N.val.obj U),
    ((((dual N).hom.val.app U) (scalarExtensionSection α (homObj N (𝒪 R)) U s f)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
        (scalarExtensionSection α N U t x) =
      s * t * α.hom.app U ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)
  dual_natural : ∀ (N P : Mod R) [N.IsInvertible] [P.IsInvertible] (f : N ⟶ P),
    changeOfRingsHomOfUniverses α _ (homObjMap f (𝟙 (𝒪 R))) ≫ (dual N).hom =
      (dual P).hom ≫ homObjMap (changeOfRingsHomOfUniverses α N f) (𝟙 (𝒪 S))
  after : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    ScalarExtensionTensorComparison S T β
  composite : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    ScalarExtensionTensorComparison R T (α ≫ β)
  tower : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (N : Mod R),
    changeOfRingsOfUniverses β (changeOfRingsOfUniverses α N) ≅
      changeOfRingsOfUniverses (α ≫ β) N
  tower_tmul : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (N : Mod R)
      (U : Cᵒᵖ) (a : T.obj.obj U) (s : S.obj.obj U) (x : N.val.obj U),
    ((tower T β N).hom.val.app U)
        (scalarExtensionSection β (changeOfRingsOfUniverses α N) U a
          (scalarExtensionSection α N U s x)) =
      scalarExtensionSection (α ≫ β) N U (a * β.hom.app U s) x
  tower_power : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (r : ℕ),
    changeOfRingsHomOfUniverses β (changeOfRingsOfUniverses α (scalarTensorPower R M r))
        (power M r).hom ≫
        ((after T β).power (changeOfRingsOfUniverses α M) r).hom ≫
        scalarTensorPowerMap T (tower T β M).hom r =
      (tower T β (scalarTensorPower R M r)).hom ≫ ((composite T β).power M r).hom
  dual_after : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    changeOfRingsOfUniverses β (homObj (changeOfRingsOfUniverses α M) (𝒪 S)) ≅
      homObj (changeOfRingsOfUniverses β (changeOfRingsOfUniverses α M)) (𝒪 T)
  dual_after_tmul : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (U : Cᵒᵖ)
      (a b : T.obj.obj U)
      (f : (homObj (changeOfRingsOfUniverses α M) (𝒪 S)).val.obj U)
      (x : (changeOfRingsOfUniverses α M).val.obj U),
    ((((dual_after T β).hom.val.app U)
        (scalarExtensionSection β (homObj (changeOfRingsOfUniverses α M) (𝒪 S)) U a f)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
        (scalarExtensionSection β (changeOfRingsOfUniverses α M) U b x) =
      a * b * β.hom.app U ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)
  dual_composite : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    changeOfRingsOfUniverses (α ≫ β) (homObj M (𝒪 R)) ≅
      homObj (changeOfRingsOfUniverses (α ≫ β) M) (𝒪 T)
  dual_composite_tmul : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (U : Cᵒᵖ)
      (a b : T.obj.obj U) (f : (homObj M (𝒪 R)).val.obj U) (x : M.val.obj U),
    ((((dual_composite T β).hom.val.app U)
        (scalarExtensionSection (α ≫ β) (homObj M (𝒪 R)) U a f)).app
        (Opposite.op (Over.mk (𝟙 U.unop))))
        (scalarExtensionSection (α ≫ β) M U b x) =
      a * b * (α ≫ β).hom.app U ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)
  dual_tower : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    changeOfRingsOfUniverses β (changeOfRingsOfUniverses α (homObj M (𝒪 R))) ≅
      changeOfRingsOfUniverses (α ≫ β) (homObj M (𝒪 R))
  dual_tower_tmul : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T) (U : Cᵒᵖ)
      (a : T.obj.obj U) (s : S.obj.obj U) (f : (homObj M (𝒪 R)).val.obj U),
    ((dual_tower T β).hom.val.app U)
        (scalarExtensionSection β (changeOfRingsOfUniverses α (homObj M (𝒪 R))) U a
          (scalarExtensionSection α (homObj M (𝒪 R)) U s f)) =
      scalarExtensionSection (α ≫ β) (homObj M (𝒪 R)) U (a * β.hom.app U s) f
  tower_dual : ∀ (T : Sheaf J CommRingCat.{u}) (β : S ⟶ T),
    changeOfRingsHomOfUniverses β _ (dual M).hom ≫ (dual_after T β).hom =
      (dual_tower T β).hom ≫ (dual_composite T β).hom ≫
        homObjMap (tower T β M).hom (𝟙 (𝒪 T))

end SheafOfModules
