/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.CategoryTheory.SystemGrothendieck
import Sheaf.CategoryTheory.DerivedCategory.ExactFunctorCoproducts
import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse

/-! # Arbitrary coproducts of strict systems and their derived evaluations

Source: Stacks 07D9; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Coproducts of arbitrary coefficient-universe size exist in the derived system category.
Source: Stacks 07D9 (blueprint: lem-pur-system-coproducts).
Proof: strict systems are Grothendieck abelian, hence have K-injective resolutions.
Termwise coproducts represent derived coproducts by maps into those resolutions. -/
theorem strictRingSystem_derivedCoproducts :
    HasCoproducts.{w} (DerivedCategory (StrictRingSystem B)) := by
  have := strictRingSystem_isGrothendieckAbelian B
  exact derived_hasCoproducts

/-- Each coefficient-level derived category has arbitrary small coproducts.
Source: Stacks 07D9 (blueprint: lem-pur-system-coproducts).
Proof: module sheaves are Grothendieck abelian, so the K-injective coproduct construction
applies to each coefficient ring. -/
theorem systemLevel_derivedCoproducts (n : ℕ) :
    HasCoproducts.{w} (DerivedCategory (systemLevel B n)) := by
  have : IsGrothendieckAbelian.{w} (systemLevel B n) :=
    isGrothendieckAbelian_coefficientUniverse _
  exact derived_hasCoproducts

/-- Exact derived evaluation preserves coproducts over every coefficient-universe index set.
Source: Stacks 07D9 and 015F (blueprint: lem-pur-system-coproducts).
Proof: ordinary evaluation preserves the componentwise colimits. Both source and target
have K-injective resolutions. Apply exact derived coproduct preservation, using the
specified exact derived evaluation and its canonical factorization. -/
theorem derivedSystemEvaluation_coproducts (n : ℕ) (I : Type w) :
    PreservesColimitsOfShape (Discrete I) (derivedSystemEvaluation B n) := by
  have := strictRingSystem_isGrothendieckAbelian B
  have : IsGrothendieckAbelian.{w} (systemLevel B n) :=
    isGrothendieckAbelian_coefficientUniverse _
  have := systemEvaluation_colimitsOfShape B (Discrete I) n
  exact (systemEvaluation B n).mapDerivedCategory_preservesCoproducts I

end SheafOfModules
