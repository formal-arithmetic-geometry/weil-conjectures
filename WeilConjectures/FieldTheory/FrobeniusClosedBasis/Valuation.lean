/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WeilConjectures.FieldTheory.FrobeniusClosedBasis.Filtration

/-!
# Frobenius-closed bases from a family of discrete valuations

Let `k` be a perfect field of characteristic `p` and `E ⊇ k` a field. Given a family of
`ℤᵐ⁰`-valued valuations on `E`, trivial on `k`, such that every element has bounded pole
orders and the elements without poles are exactly the constants, the pole-order filtration
satisfies the hypotheses of `FrobeniusClosedBasis.exists_frobeniusClosed_basis_of_filtration`,
so `E` has a Frobenius-closed `k`-basis.
-/

@[expose] public section

universe v

open Submodule
open scoped WithZero

namespace FrobeniusClosedBasis

variable {k : Type*} {E : Type v} [Field k] [Field E] [Algebra k E]

end FrobeniusClosedBasis
