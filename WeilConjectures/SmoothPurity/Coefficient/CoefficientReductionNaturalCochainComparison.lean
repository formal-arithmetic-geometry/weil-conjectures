/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison

/-! # The natural cochain comparison for completed-coefficient reduction

Source: Stacks 07A6, 09T5, 0D6E and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : Scheme.{t})

namespace ReductionCochainComparison

set_option backward.defeqAttrib.useBackward true

-- The cone of ordinary inverse-limit projections in each degree.

end ReductionCochainComparison

end WeilConjectures
