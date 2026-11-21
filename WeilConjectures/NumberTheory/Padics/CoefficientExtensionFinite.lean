/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Finiteness interface for finite p-adic coefficient extensions

Source: Serre, Local Fields, Chapter II, §2 (auxiliary.

The coefficient constructions are imported unchanged; this supplies their finite-ring
interface at positive levels.
-/

@[expose] public section

universe u

namespace Padic

/-- The coefficient ring at a finite level is finite.

Source: Serre, Local Fields, Chapter II, §2 (auxiliary.
-/
theorem finite_coefficientExtensionRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n) :
    Finite (Padic.coefficientExtensionRing l E n) := by
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hfinite : Finite (coefficientExtensionIntegers l E ⧸
      coefficientExtensionMaximalIdeal l E) :=
    h.2.2.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} :
      Set (coefficientExtensionIntegers l E)) = coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : Finite (coefficientExtensionIntegers l E ⧸
      Ideal.span ({coefficientExtensionUniformizer l E} :
        Set (coefficientExtensionIntegers l E))) := by
    rw [hgen]
    exact hfinite
  exact Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) n

end Padic
