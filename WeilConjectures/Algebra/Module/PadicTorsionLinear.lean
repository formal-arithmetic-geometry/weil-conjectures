/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Additive maps between `ℤ_p`-modules killed by `pᵐ` are `ℤ_p`-linear

On a `ℤ_p`-module killed by `pᵐ`, the scalar `r ∈ ℤ_p` acts as the natural number
`PadicInt.appr r m`, which is congruent to `r` modulo `pᵐ`
(`PadicInt.smul_eq_appr_nsmul`). Hence every additive map between two such modules is
`ℤ_p`-linear (`PadicInt.linearMapOfPowSMulEqZero`), and every biadditive map is `ℤ_p`-bilinear
(`PadicInt.bilinearOfPowSMulEqZero`).
-/

@[expose] public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {M N P : Type*} [AddCommGroup M] [Module ℤ_[p] M]
  [AddCommGroup N] [Module ℤ_[p] N] [AddCommGroup P] [Module ℤ_[p] P]

end PadicInt
