/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Assembly of the normalized derived projection data

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md`, coefficient-comparison paragraph, via the original
sequence-projection normalization proof steps
(blueprint: lem-pur-sequence-derived-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
The supplied finite-field coefficient calculus and ordinary ringed projection admit the
normalized derived adjoint data.  The fields of `PurSequenceDerivedAdjoints` record the
universal left and right derived comparisons, their strict K-flat and K-injective models,
the adjunction unit and counit normalizations, and the canonical comparison for every
simultaneous tower replacement.

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md`, coefficient-comparison paragraph, via the original
sequence-projection normalization proof steps.  The statement packages the following
steps: (1) obtain the universal K-injective comparison, its map to total inverse limit,
and the compatible K-flat comparison; (2) identify the left comparison with the supplied
reduction and the right comparison with the ordinary limit identification followed by
those universal comparisons; (3) transport the adjunction, unit, counit, and
Hom-normalization equations along these identifications; and (4) use the arbitrary
replacement isomorphism and functoriality to obtain the model equality and the normalized
`lim (j)` composition equation.  These are the clauses represented by the returned
`PurSequenceDerivedAdjoints` structure.
(blueprint: lem-pur-sequence-derived-normalization).
-/
theorem purSequenceDerivedNormalization
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (H : PurSequenceRingedFactorization l E W O) :
    Nonempty (PurSequenceDerivedAdjoints l E W S O) := by
  sorry

end WeilConjectures
