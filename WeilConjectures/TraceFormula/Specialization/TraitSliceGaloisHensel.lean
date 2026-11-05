/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Polynomial.Identities

/-!

# Newton's lemma over power series rings

Two elementary inputs to the comparison of the Laurent series fields `k'((t)) ⊆ K((t))` of the
generic slices (SGA 4½, [Th. finitude], Lemme 3.3):

* **Hensel's lemma without monicity** (`IsAdicComplete.exists_isRoot_sub_mem`): over an
  `I`-adically complete ring, a polynomial `f` with `f(a₀) ∈ I` and `f'(a₀)` a unit modulo `I` has
  a root `a ≡ a₀ (mod I)`. Mathlib's `HenselianRing` only states this for monic `f`, although the
  Newton iteration proving `IsAdicComplete.henselianRing` does not use monicity.
* **Newton's lemma** (`Polynomial.exists_isRoot_powerSeries_of_sq_mul_X_dvd`): over `k⟦t⟧`, `k` a
  field, if `f'(β)² t ∣ f(β)` then `f` has a root `γ` with `f'(β) t ∣ γ - β`; and the root is
  unique in the sense of `Polynomial.eq_or_sub_dvd_derivative_eval_of_isRoot`: two roots
  `a ≠ b` of `f` in a domain satisfy `a - b ∣ f'(a)`.

-/

@[expose] public section

open Polynomial
open scoped Ring

