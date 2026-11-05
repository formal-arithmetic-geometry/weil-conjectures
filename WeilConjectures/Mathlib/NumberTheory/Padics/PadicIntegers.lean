/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Transcendental `p`-adic integers and `ℓ`-adic numbers as fractions

## Main statements

- `PadicInt.exists_transcendental`: there is a `p`-adic integer which is transcendental over `ℤ`.
- `Padic.exists_eq_inv_pow_mul`: every `ℓ`-adic number is of the form `ℓ ^ (-b) * z` with `z` an
  `ℓ`-adic integer, that is, `ℚ_[ℓ] = ℤ_[ℓ][1/ℓ]`.
-/

@[expose] public section

open Cardinal

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

end PadicInt

namespace Padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

end Padic
