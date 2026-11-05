/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationOrdinaryCoherence
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedCore
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientScalarDerivedAdjunction
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.CompositeMate
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-!
# Derived extension and coherence relative to a strict evaluation adjunction

Source: Zheng, Construction 4.1, p. 21; Stacks Project, Tags 06XN, 0FND and 09T5.
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

local notation "ev" => coefficientEvaluation (J := J) (O := O) (ell := ell)
local notation "tensor" => coefficientTensor (J := J) (O := O) (ell := ell)
local notation "tensorAdj" => coefficientTensorAdj (J := J) (O := O) (ell := ell)

attribute [local irreducible] coefficientEvaluationSigma

end SheafOfModules
