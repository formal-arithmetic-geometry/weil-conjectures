/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!
# Separably closed fields and separable closures

Separably closed fields and separable closures are Mathlib's `IsSepClosed` and `IsSepClosure`.
This file records the equivalent formulations of separable closedness used for the geometric
points of the small étale site: every separable polynomial splits, every nonconstant separable
polynomial has a root, and there is no nontrivial finite separable extension.
-/

@[expose] public section

universe u

open Polynomial

namespace IsSepClosed

variable (k : Type u) [Field k]

/-- Blueprint `def-kun-separably-closed`: Separably closed fields

The following are equivalent for a field `k`:
1. `k` is separably closed (Mathlib's `IsSepClosed k`);
2. every separable polynomial over `k` splits over `k`;
3. every nonconstant separable polynomial over `k` has a root in `k`;
4. `k` admits no nontrivial finite separable field extension.

A separable closure of `k` is a separable algebraic extension whose top field is separably closed
(`isSepClosure_iff`). -/
theorem tfae : List.TFAE [IsSepClosed k, ∀ p : k[X], p.Separable → p.Splits,
    ∀ p : k[X], p.degree ≠ 0 → p.Separable → ∃ x, p.IsRoot x,
    ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K],
      Module.finrank k K = 1] := by
  tfae_have 1 ↔ 2 := ⟨fun h ↦ h.splits_of_separable, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 3 := iff_exists_root k
  tfae_have 1 ↔ 4 := iff_forall_finrank_eq_one k
  tfae_finish

/-- Blueprint `def-kun-separably-closed`: a separable closure of `k` is a separable algebraic
extension `K / k` whose top field `K` admits no nontrivial finite separable extension. -/
theorem _root_.isSepClosure_iff_forall_finrank_eq_one (K : Type u) [Field K] [Algebra k K] :
    IsSepClosure k K ↔ Algebra.IsSeparable k K ∧
      ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
        [Algebra.IsSeparable K L], Module.finrank K L = 1 := by
  rw [isSepClosure_iff, iff_forall_finrank_eq_one K, and_comm]

end IsSepClosed
