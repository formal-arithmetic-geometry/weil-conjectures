/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.FrobeniusClosedBasis
public import WeilConjectures.FieldTheory.AdjoinSimplePow

/-!
# Frobenius-closed bases of function fields inside a bigger field

Let `ℓ` be a field of characteristic `p`, `k ≤ E` subfields of `ℓ` with `k` algebraically closed,
and `x ∈ E` transcendental over `k` such that `E` is a finite separable extension of `k⟮x⟯`.
Then `E` has a Frobenius-closed `k`-basis `1, w i ^ p ^ n`
(`FrobeniusClosedBasis.exists_frobeniusClosed_basis`), and `x` is a polynomial of degree `< p`
with coefficients in `E ^ p` in any element `ρ ∈ E` which is not a `p`-th power in `E`: indeed
`E = E ^ p (x)` has degree `p` over `E ^ p`, so `E = E ^ p (ρ)`.
-/

@[expose] public section

universe u

open Polynomial IntermediateField

namespace FrobeniusClosedBasis

end FrobeniusClosedBasis
