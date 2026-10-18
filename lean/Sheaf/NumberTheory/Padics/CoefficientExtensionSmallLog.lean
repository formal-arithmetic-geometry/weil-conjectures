/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The small logarithm without a chosen algebraic-closure embedding

Source: Weil conjectures blueprint, main-20261015, sec-purity-real-sheaves,
sk-d-real-log, displayed logarithm series (blueprint: sk-d-real-log).

The spectral norm is the uniquely extended adic absolute value of the recorded coefficient
extension. This gives the same series as `PadicAlgCl.smallLog` without choosing an embedding
of the coefficient field into the algebraic closure. The input is `x`, so the value is
`log (1 + x)`, and its specified domain is `x ∈ ℓ² 𝒪_E`.
-/

@[expose] public section

universe u

namespace Padic

/-- The small principal-unit domain `1 + ℓ² 𝒪_E`, as a subset of the coefficient-field units.
The integer ring is the recorded coefficient extension's integer ring.
Source: blueprint main-20261015, sk-d-real-log, defining display
(blueprint: sk-d-real-log). -/
def coefficientExtensionSmallUnits (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    Set Eˣ :=
  {z | ∃ a : coefficientExtensionIntegers ℓ E, (z : E) = 1 + (ℓ : E) ^ 2 * (a : E)}

/-- The series `log (1 + x) = ∑ₙ (-1)^n x^(n+1)/(n+1)` in the uniquely extended adic
 topology on a finite coefficient extension. Its small domain is `x ∈ ℓ² 𝒪_E`.
Source: blueprint main-20261015, sk-d-real-log, defining display
(blueprint: sk-d-real-log). -/
noncomputable def coefficientExtensionSmallLog (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (x : E) : E :=
  letI := spectralNorm.normedField (Padic ℓ) E
  ∑' n : ℕ, (-1 : E) ^ n * x ^ (n + 1) / (n + 1 : ℕ)

end Padic
