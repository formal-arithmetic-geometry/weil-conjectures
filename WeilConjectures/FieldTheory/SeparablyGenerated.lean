/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Separably generated and separable field extensions

Following Stacks, Algebra, Definitions 030O and 030P (for not necessarily algebraic
extensions):

- `Algebra.IsSeparablyGenerated k K`: there is a transcendence basis `(x_i)` of `K/k` such that
  `K/k(x_i)` is separable algebraic;
- `Algebra.IsSeparableExtension k K`: every finitely generated subextension is separably
  generated.
-/

@[expose] public section

namespace Algebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- `K/k` is *separably generated* if there is a transcendence basis `s` of `K/k` such that
`K/k(s)` is separable algebraic. (blueprint: `def-weil-pbc-separable-field-extension`) -/
def IsSeparablyGenerated : Prop :=
  ∃ s : Set K, IsTranscendenceBasis k ((↑) : s → K) ∧
    Algebra.IsSeparable (IntermediateField.adjoin k s) K

/-- `K/k` is *separable* if every subextension `k ⊆ K' ⊆ K` which is finitely generated as a field
over `k` is separably generated. (blueprint: `def-weil-pbc-separable-field-extension`) -/
def IsSeparableExtension : Prop :=
  ∀ K' : IntermediateField k K, K'.FG → IsSeparablyGenerated k K'

end Algebra
