/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!

# Kummer normal forms over a Frobenius-closed lifted basis (mixed characteristic)

Let `Ω` be a field with a valuation `v` and `p` a prime with `0 < v p < 1` (mixed
characteristic), `K ≤ L₁ ≤ L₂` subfields with `K` closed under `p`-th roots, and `w : ι → L₁` a
family of units which is valuation independent over `K`. We show that a `1`-unit `u ∈ L₁ ∩ L₂^p`
is a `p`-th power in `L₁` (`exists_pow_eq_of_approx`), given approximations of the elements of
`L₁` by `K`-combinations of the `w i ^ p ^ n` and the usual residual hypothesis `hres` on `L₂`.

The proof follows F.-V. Kuhlmann, *Elimination of ramification I*, Trans. AMS 362 (2010),
Prop. 4.16, in two stages, where an element `x` is *negligible* if `v x ^ (p - 1) ≤ v p ^ p`
(i.e. its additive value is at least `p v(p)/(p-1)`), so that `1 + x` is a `p`-th power by
Hensel's lemma:
* stage 1, for terms of value `≥ v p`: modulo `1 + p𝔪`, `(1 + c) ^ p ≡ 1 + c ^ p`; the leading
  terms are `p`-th powers of lifted basis elements, which are cancelled exactly; the values of
  the terms stay in a finitely generated monoid, so the process terminates;
* stage 2, for terms of value `< v p`: modulo negligible elements the problem is linear, and a
  term `d w ^ p ^ (n + 1)` is replaced by `- p d^{1/p} w ^ p ^ n`.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation Ω Γ₀) (p : ℕ)

/-- An element is *negligible* (for the Kummer theory of exponent `p`) if its additive value is
at least `p v(p) / (p - 1)`. -/
def Valuation.IsKummerNegligible (x : Ω) : Prop :=
  v x ^ (p - 1) ≤ v (p : Ω) ^ p

namespace Valuation.IsKummerNegligible

variable {v p}

end Valuation.IsKummerNegligible

namespace Valuation

variable {v}

end Valuation

section Stage2

variable {v p} {ι : Type*} (w : ι → Ω)

end Stage2

section Stage2Step

variable {v p} {ι : Type*} {w : ι → Ω}

end Stage2Step

section Stage2Base

variable {v p} {ι : Type*} {w : ι → Ω} (K L₁ L₂ : Subfield Ω)

end Stage2Base

section Stage2Main

variable {v p} {ι : Type*} {w : ι → Ω} (K L₁ L₂ : Subfield Ω)

end Stage2Main
