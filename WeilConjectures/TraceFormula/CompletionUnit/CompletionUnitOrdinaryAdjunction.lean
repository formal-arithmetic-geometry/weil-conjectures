/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization

/-! # The ordinary coefficient tensor and inverse-limit adjunction

Source: Stacks 03D7 and 0941, and canonical-model construction step 1.
(blueprint: lem-trf-completion-unit-ordinary-adjunction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

section OrdinaryConstruction
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf

end OrdinaryConstruction

section CanonicalComparisons

-- The cone of ordinary inverse-limit projections in each degree.

end CanonicalComparisons

end WeilConjectures.CompletionUnit
