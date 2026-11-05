/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!

# Artin–Schreier normal forms over a Frobenius-closed lifted basis

Let `Ω` be a field of characteristic `p` with a valuation `v`, and `K ≤ L₁ ≤ L₂` subfields of `Ω`,
where `K` is perfect and Artin–Schreier closed. Let `w : ι → L₁` be a family of elements of value
`1`, *valuation independent* over `K`: the value of a `K`-combination `∑ cᵢ wᵢ` is at least the
value of each coefficient. The elements `w i ^ p ^ n` play the role of the lifts of a
Frobenius-closed basis of the residue field (Kuhlmann).

The Artin–Schreier class of an element of `L₁` approximated, up to an error of value `≤ 1`, by
`d₀ + ∑ d_{i,n} w i ^ p ^ n` (`dᵢₙ ∈ K`) is that of `∑ dᵢₙ^{1/pⁿ} wᵢ`, by the telescoping identity
`X^{pⁿ} - X = ∑_{m<n} ℘(X^{p^m})` (`℘ X = X ^ p - X`). If such an element is in `℘(L₂)` and the
residues of the `wᵢ` are never congruent to a `p`-th power of an element of `L₂` (the hypothesis
`hres`), then the leading coefficients vanish, so the element lies in `℘(L₁)`
(`AddValuation`-free statement: `exists_artinSchreier_root_of_approx`).

This is the equal-characteristic case of the stability argument of F.-V. Kuhlmann, *Elimination
of ramification I: the generalized stability theorem*, Trans. AMS 362 (2010), Prop. 4.14.

-/

@[expose] public section

open Finset

variable {Ω : Type*} [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]

section NormalForm

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation Ω Γ₀)
  (K L₁ L₂ : Subfield Ω) {ι : Type*} (w : ι → Ω)

end NormalForm
