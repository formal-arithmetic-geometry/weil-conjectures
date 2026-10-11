/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Descent of an annihilator from localization at a finitely generated prime

Source: Stacks Project, Algebra, Tag 0310 (2), used in Tag 058A
(blueprint: lem-sc-associated-localization-fg).
-/

@[expose] public section

universe u v

namespace Module

/-- If the maximal ideal of `Rₚ` is the annihilator of an element of `Mₚ`, and `p` is
finitely generated, then `p` is the annihilator of an element of `M`.
Source: Stacks Project, Algebra, Tag 0310 (2), used in Tag 058A
(blueprint: lem-sc-associated-localization-fg).

Proof (using def-weil-pbc-localization-at-prime and def-weil-pbc-module-localization):
1. Write the localized element as `m/s` and `p = (f₁, ..., fₙ)`. If `a` annihilates `m`,
then `a/1` annihilates `m/s`. Contracting the maximal ideal of `Rₚ` gives `p`, so
`Ann_R(m) ⊆ p`.
2. For each generator `fᵢ`, clear a denominator to obtain `uᵢ ∉ p` with `uᵢ fᵢ m = 0`.
Set `u = ∏ uᵢ` and `m' = u m`. Every generator kills `m'`, and `u ∉ p`. Also `m' ≠ 0`,
since otherwise the unit `u/1` would annihilate `m/s`.
3. Thus `p ⊆ Ann_R(m')`. Conversely, if `a m' = 0`, then `au ∈ Ann_R(m) ⊆ p`.
Primality and `u ∉ p` imply `a ∈ p`, proving `Ann_R(m') = p`. -/
theorem exists_annihilator_eq_of_localization_atPrime
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (hp : p.FG)
    (h : ∃ z : LocalizedModule.AtPrime p M,
      IsLocalRing.maximalIdeal (Localization.AtPrime p) =
        (⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon {z}) :
    ∃ m : M, p = (⊥ : Submodule R M).colon {m} := by
  sorry

end Module
