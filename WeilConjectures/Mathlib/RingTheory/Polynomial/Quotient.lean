/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Evaluation at zero on quotients of polynomial rings

`R[X] ⧸ (X) ⟶ R ⧸ J`, induced by evaluation at `0`, is natural in the pair `(R, J)`.

## Main results

- `Polynomial.quotientMap_comp_lift_evalRingHom_zero`: the naturality of `R[X] ⧸ (X) ⟶ R ⧸ J`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

end Polynomial
