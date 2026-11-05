/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso

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

attribute [irreducible] scalarExtensionTowerIso

end Universes

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] in
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] changeOfRingsOfUniverses scalarExtensionSection
  siteSheafTensorTmul siteSheafTensorRight siteSheafTensorSecondMap

attribute [local irreducible] scalarExtensionTowerForward scalarExtensionTowerReverse

end SheafOfModules
