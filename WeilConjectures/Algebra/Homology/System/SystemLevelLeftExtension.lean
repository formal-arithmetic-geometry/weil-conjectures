/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
import WeilConjectures.Algebra.Homology.System.SystemCoproducts
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedComposition
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransitionUnit
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedTransition
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedCompositionEvaluation

/-! # Derived left extensions of strict semilinear systems

Source: Zheng, Construction 4.1; Stacks 06XN, 0FND and 09T5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

-- Unused-variable linting needlessly normalizes the entire extension schema here.

end SheafOfModules
