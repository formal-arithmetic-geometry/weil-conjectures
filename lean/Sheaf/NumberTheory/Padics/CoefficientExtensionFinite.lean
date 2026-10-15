/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtension
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finiteness interface for finite p-adic coefficient extensions

Source: Weil blueprint, `def-weil-finite-field-fiber`, order 411;
Serre, Local Fields, Chapter II, §2
(blueprint: def-weil-l-adic-coefficient-extension).

The coefficient constructions are imported unchanged; this supplies their finite-ring
interface at positive levels.
-/

@[expose] public section

universe u

namespace Padic

/-- The coefficient ring at a finite level is finite.

Source: Weil conjectures blueprint, node `def-weil-finite-field-fiber`,
order 411; Serre, Local Fields, Chapter II, §2
(blueprint: def-weil-l-adic-coefficient-extension).

Proof: Apply `Padic.extension_integers_dvr` to the spectral absolute value to obtain
that the recorded integer ring is a DVR with finite residue field. Its recorded
uniformizer generates the recorded maximal ideal. Thus the ideal defining the level
`n` ring is the `n`th power of that maximal ideal. Each successive ideal quotient
is a finite-dimensional vector space over the finite residue field, and induction
on `n` gives the finiteness of the ring quotient. Equivalently apply
`Ideal.finite_quotient_pow` in the Noetherian integer ring after identifying ideals.
-/
theorem finite_coefficientExtensionRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n) :
    Finite (Padic.coefficientExtensionRing l E n) := by
  sorry

end Padic
