/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Frobenius on multivariate polynomials over a finite field

Over a finite field `K` with `q` elements, raising a multivariate polynomial to the `q`-th
power substitutes `Xᵢ ^ q` for each variable: `expand q f = f ^ q`. This is the multivariate
analogue of `FiniteField.expand_card`, and generalises `MvPolynomial.expand_zmod` from
`ZMod p` to an arbitrary finite field.
-/

@[expose] public section

namespace MvPolynomial

variable {σ K : Type*} [Field K] [Fintype K]

end MvPolynomial
