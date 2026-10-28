/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Finite p-adic coefficient extensions

Source: Weil conjectures blueprint, `def-weil-finite-field-fiber`, order 411;
slopmaster2, Definition `def:weil-finite-coefficient-datum`
(auxiliary; not a blueprint node).

The absolute value is the spectral absolute value. The ring of integers, its maximal
ideal, and one uniformizer are selected from `Padic.extension_integers_dvr`.
The claims about these data are the separately cited dependency theorems.
-/

@[expose] public section

universe u

namespace Padic

/-- The unique absolute value extending the p-adic absolute value, given by the spectral norm.
Its uniqueness, nonarchimedean property and completeness are the cited Mathlib facts.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (auxiliary; not a blueprint node). -/
noncomputable def coefficientExtensionAbsoluteValue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    AbsoluteValue E ℝ :=
  MulRingNorm.mulRingNormEquivAbsoluteValue (spectralMulAlgNorm ℚ_[l] E).toMulRingNorm

/-- The valuation ring `𝒪_E = {x : E | |x|_E ≤ 1}`, selected from the DVR theorem.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (auxiliary; not a blueprint node). -/
noncomputable def coefficientExtensionIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Subring E :=
  (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose

end Padic
