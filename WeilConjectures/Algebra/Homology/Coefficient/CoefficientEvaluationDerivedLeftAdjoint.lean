/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedExtension
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedAbove
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedBelow
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedTransition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientTensorDerivedUnit

/-!
# Derived extension from a coefficient level
Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
Stacks Project, Tags 03D7, 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint).
Indices in this module are Zheng's nonnegative indices: `n` denotes the paper node's
positive level `n + 1`. No normalization or cartesianness is imposed on a system.
The auxiliary declarations construct the actual strict systems and their evaluations;
the final package records the constructions, universal properties and all coherence laws.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  {O : Type w} [CommRing O] {ell : O} [EssentiallySmall.{w} C]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

-- The original signature retains regularity, although this construction does not need it.
end SheafOfModules
