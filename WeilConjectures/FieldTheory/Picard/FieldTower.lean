/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Field extensions and towers

## Main definitions

* `FieldExtension.degree` is the vector-space degree, with `⊤` for an infinite
  dimensional extension.

## Implementation details

Finite, algebraic, finite separable, purely inseparable extensions and algebraic closures are
expressed by Mathlib's existing notions `Module.Finite k K`, `Algebra.IsAlgebraic k K`,
`Module.Finite k K ∧ Algebra.IsSeparable k K`, `IsPurelyInseparable k K`, and
`IsAlgClosure k K`, respectively.

## References

* Stacks Project, Fields, Tags 09FV, 09GC, 09G3, 09H1, 09HE, and 09GS
-/

@[expose] public section

universe u v

namespace FieldExtension

/-- The degree `[K : k]`: `Module.finrank k K` when `K` is finite-dimensional over `k`,
and `⊤` otherwise. -/
noncomputable def degree (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] :
    WithTop ℕ := by
  classical
  exact if Module.Finite k K then (Module.finrank k K : WithTop ℕ) else ⊤

end FieldExtension
