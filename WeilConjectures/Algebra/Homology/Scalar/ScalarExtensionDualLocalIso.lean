/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualEvaluation
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Scalar extension of a locally free rank-one module

Source: Stacks Project, Tags 03EK, 03EM, 04TT.
(blueprint: lem-sp-scalar-extension-dual-local-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u m
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

attribute [local irreducible] scalarExtensionDualMap

section SliceExt

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

end SliceExt

section LocalBasis

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
  (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

set_option hygiene false in
local notation:max "𝒪" R:arg => unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

section DualInverse

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]

end DualInverse

end LocalBasis

end SheafOfModules
