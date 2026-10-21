/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic
import Sheaf.CategoryTheory.SystemRingedSequenceSite
import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse

/-! # Grothendieck abelian strict coefficient systems

Source: Zheng, Construction 4.1; Stacks 03DA, 03DB and 079Q.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- Strict coefficient systems form a Grothendieck abelian category.
Source: Zheng 4.1; Stacks 03DA, 03DB and 079Q
(blueprint: lem-pur-system-grothendieck).
Proof: the ringed sequence site is essentially small in the coefficient universe.
Its module sheaves are Grothendieck abelian by the free-sheaf separator and exactness
of filtered colimits. Transport this property across the explicit equivalence with
strict systems. -/
theorem strictRingSystem_isGrothendieckAbelian
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) :
    IsGrothendieckAbelian.{w} (StrictRingSystem B) := by
  let : EssentiallySmall.{w} (ℕ × C) := EssentiallySmall.mk'
    ((AsSmall.equiv : ℕ ≌ AsSmall.{w} ℕ).prod (equivSmallModel.{w} C))
  have : IsGrothendieckAbelian.{w} (systemSequenceModules B) :=
    isGrothendieckAbelian_coefficientUniverse _
  exact IsGrothendieckAbelian.of_equivalence (strictSystemSequenceEquivalence B).symm

end SheafOfModules
