/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Schemes of characteristic `p`

Source: Stacks Project, Varieties, Section 33.36 (Tag 0CC6), first paragraph before
Definition 33.36.1 (blueprint: def-weil-scheme-characteristic-p).
-/

@[expose] public section

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- A scheme is of characteristic `p` when `p` is zero in the structure sheaf on
every open subset. The prime condition is included in the predicate, and the
empty scheme satisfies it for every prime.
Source: Stacks Project, Varieties, Section 33.36 (Tag 0CC6), first paragraph before
Definition 33.36.1 (blueprint: def-weil-scheme-characteristic-p). -/
def Scheme.IsCharacteristic (X : Scheme.{u}) (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∀ U : X.Opens, (p : Γ(X, U)) = 0

end AlgebraicGeometry
