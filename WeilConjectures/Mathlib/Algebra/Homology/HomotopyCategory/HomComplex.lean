/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Complements on the hom complex

The type `CochainComplex.HomComplex.Triplet n` of pairs of integers `(p, q)` with
`p + n = q` is countable.
-/

@[expose] public section

namespace CochainComplex.HomComplex

instance (n : ℤ) : Countable (Triplet n) :=
  Function.Injective.countable (f := fun T : Triplet n ↦ (T.p, T.q))
    (by rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h; cases h; rfl)

end CochainComplex.HomComplex
