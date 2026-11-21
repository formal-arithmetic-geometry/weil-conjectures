/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.InvertibleTensorScalarExtensionDefinitions

/-!
# Tensor powers and duals under scalar extension

Tensor powers and dual evaluation under ordinary scalar extension.

## References

* Stacks Project, Tag 03EK
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
Positive powers are left associated, with degree one equal to `M` as in the dependency. -/
noncomputable def scalarTensorPower (R : Sheaf J CommRingCat.{u}) (M : Mod R) : ℕ → Mod R
  | 0 => 𝒪 R
  | n + 1 => Nat.rec M (fun _ P ↦ 𝒯 P M) n

/-- Tensor power at zero is the scalar unit. -/
theorem scalarTensorPower_zero (R : Sheaf J CommRingCat.{u}) (M : Mod R) :
    scalarTensorPower R M 0 = 𝒪 R := rfl

/-- Tensor power at one is the original module. -/
theorem scalarTensorPower_one (R : Sheaf J CommRingCat.{u}) (M : Mod R) :
    scalarTensorPower R M 1 = M := rfl

/-- The map on tensor powers induced by a module morphism. -/
noncomputable def scalarTensorPowerMap
    (R : Sheaf J CommRingCat.{u}) {M N : Mod R} (f : M ⟶ N) :
    ∀ r : ℕ, scalarTensorPower R M r ⟶ scalarTensorPower R N r
  | 0 => 𝟙 _
  | 1 => f
  | n + 2 =>
      (siteSheafTensorRight M).map (scalarTensorPowerMap R f (n + 1)) ≫
        siteSheafTensorSecondMap (scalarTensorPower R N (n + 1)) f

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection
  siteSheafTensorTmul siteSheafTensorRight siteSheafTensorSecondMap

end SheafOfModules
