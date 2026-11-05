/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels

/-!
# The actual completion unit on a strict quotient cone

Source: blueprint main-20261015, trace formula, rational Frobenius integral model,
proof (2)--(3); Stacks 07A6, 09T5, 0D6E, 0941 and 08TC. This is the normalization
refinement of those constructions, not a verbatim assertion of a Stacks tag.
(blueprint: lem-trf-completion-unit-strict-quotient-model).

The auxiliary structures package canonical constructions and their normalization
conditions. They introduce no alternative tensor, limit, or derived category.
The theorem asserts their existence together with the whole-morphism unit formula.
The compatible-model construction is isolated in `canonicalModels`; the proof here
derives the cone, unit and two-resolution formulas from its normalizations.
Index n denotes the positive exponent n+1. Site and coefficient universes are independent.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures
namespace CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end CompletionUnit
end WeilConjectures
