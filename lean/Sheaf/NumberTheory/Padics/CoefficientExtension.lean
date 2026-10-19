/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Finite p-adic coefficient extensions

Source: Weil conjectures blueprint, `def-weil-finite-field-fiber`, order 411;
slopmaster2, Definition `def:weil-finite-coefficient-datum`
(blueprint: def-weil-l-adic-coefficient-extension).

The absolute value is the spectral absolute value. The ring of integers, its maximal
ideal, and one uniformizer are selected from `Padic.extension_integers_dvr`.
The claims about these data are the separately cited dependency theorems.
-/

@[expose] public section

universe u

namespace Padic

/-- The degree `[E : ℚ_[l]]` of the finite extension.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable def coefficientExtensionDegree (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ℕ :=
  Module.finrank ℚ_[l] E

/-- The unique absolute value extending the p-adic absolute value, given by the spectral norm.
Its uniqueness, nonarchimedean property and completeness are the cited Mathlib facts.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable def coefficientExtensionAbsoluteValue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    AbsoluteValue E ℝ :=
  MulRingNorm.mulRingNormEquivAbsoluteValue (spectralMulAlgNorm ℚ_[l] E).toMulRingNorm

/-- The valuation ring `𝒪_E = {x : E | |x|_E ≤ 1}`, selected from the DVR theorem.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable def coefficientExtensionIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Subring E :=
  (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose

/-- The maximal ideal `𝔪_E = {x : 𝒪_E | |x|_E < 1}` from the same DVR witness.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable def coefficientExtensionMaximalIdeal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Ideal (coefficientExtensionIntegers l E) :=
  (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose

/-- The finite residue field `k_E = 𝒪_E / 𝔪_E`.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
@[reducible]
noncomputable def coefficientExtensionResidueField (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Type u :=
  coefficientExtensionIntegers l E ⧸ coefficientExtensionMaximalIdeal l E

/-- One chosen uniformizer `ϖ_E`, generating `𝔪_E`.
The DVR theorem gives existence, the maximal-value characterization, unit association,
and the unique unit-times-integer-power expression for every nonzero field element.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable def coefficientExtensionUniformizer (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    coefficientExtensionIntegers l E :=
  (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
      |>.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose

/-- The ideal `ϖ_Eⁿ 𝒪_E`. We use `(span {ϖ_E})ⁿ`, equal to `span {ϖ_Eⁿ}` by
`Ideal.span_singleton_pow`, and equal to `𝔪_Eⁿ` since the chosen element generates `𝔪_E`.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable def coefficientExtensionIdeal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Ideal (coefficientExtensionIntegers l E) :=
  Ideal.span ({coefficientExtensionUniformizer l E} :
    Set (coefficientExtensionIntegers l E)) ^ n

/-- The finite coefficient ring `A_{E,n} = 𝒪_E / ϖ_Eⁿ 𝒪_E`, for `n ≥ 1`.
The formula also makes sense at `n = 0`, where it gives the zero ring.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
@[reducible]
noncomputable def coefficientExtensionRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Type u :=
  coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n

/-- The transition homomorphism `A_{E,n+1} → A_{E,n}`, induced by the identity on `𝒪_E`.
It is the quotient factor map for the inclusion of successive powers, hence surjective
by `Ideal.Quotient.factor_surjective`.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
noncomputable def coefficientExtensionTransition (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    coefficientExtensionRing l E (n + 1) →+* coefficientExtensionRing l E n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))

end Padic
