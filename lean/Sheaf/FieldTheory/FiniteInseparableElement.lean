/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.FieldTheory.FieldTower
public import Sheaf.FieldTheory.SeparableExtension
public import Mathlib.FieldTheory.Separable

/-!
# An inseparable element in a finite nonseparable field extension

Source: Stacks Project, Algebra, Definition 10.42.1 (Tag 030O), applied to a finite extension
(blueprint: lem-pc-finite-inseparable-element).
-/

@[expose] public section

universe u v

namespace FieldExtension

/-- (blueprint: lem-pc-finite-inseparable-element) A finite field extension that is not
separable has an element whose minimal polynomial is inseparable.

For the contrapositive, assume every element has a separable minimal polynomial. Each
finitely generated intermediate field is finite-dimensional over the base, hence algebraic.
Its elements remain separable over the base. The empty transcendence basis therefore makes
each such field separably generated. By Definition 10.42.1 (Tag 030O), the whole extension
is separable, contrary to the hypothesis. -/
theorem exists_not_isSeparable_of_not_isSeparableExtension
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (hfinite : degree k K ≠ ⊤) (hnot : ¬ Algebra.IsSeparableExtension k K) :
    ∃ α : K, ¬ IsSeparable k α := by
  sorry

end FieldExtension
