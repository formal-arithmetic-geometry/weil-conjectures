/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Powers in the fraction field of an integrally closed domain

## Main statements

- `IsIntegrallyClosed.not_exists_pow_eq_algebraMap`: if `R` is an integrally closed domain with
  fraction field `K` and `a ∈ P \ P ^ 2` for a prime ideal `P` of `R`, then `a` is not an `n`-th
  power in `K` for any `2 ≤ n`.
-/

@[expose] public section

open Polynomial

