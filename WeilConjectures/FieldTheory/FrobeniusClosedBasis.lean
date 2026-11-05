/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WeilConjectures.FieldTheory.FrobeniusClosedBasis.Dedekind
public import WeilConjectures.FieldTheory.FrobeniusClosedBasis.Valuation

/-!
# Frobenius-closed bases of function fields

Let `k` be an algebraically closed field of characteristic `p`, and let `E` be a finite separable
extension of `k⟮x⟯` with `x` transcendental over `k`. Then `E` has a *Frobenius-closed*
`k`-basis: there is a family `w : ι → E` such that `1` together with the `w i ^ p ^ r`
(`i : ι`, `r : ℕ`) form a `k`-basis of `E`.

As a consequence, if `c₀ + ∑ cᵢ wᵢ` is a `p`-th power in `E`, then all `cᵢ` vanish.

Source: F.-V. Kuhlmann, *Additive polynomials and their role in the model theory of valued
fields*, arXiv:1003.5683, Theorem 10, Lemmas 25 and 26.

## Proof

The pole orders at the height-one primes of the integral closures of `k[x]` and `k[x⁻¹]` in `E`
define a filtration of `E` by `k`-subspaces, with `0`-th step `k`, compatible with Frobenius
(`FrobeniusClosedBasis.exists_valuations_of_transcendental`). A Frobenius-closed basis is then
constructed level by level (`FrobeniusClosedBasis.exists_frobeniusClosed_basis_of_filtration`).
-/

@[expose] public section

universe v

open Polynomial IntermediateField Submodule

namespace FrobeniusClosedBasis

variable {k : Type*} {E : Type v} [Field k] [Field E] [Algebra k E]

end FrobeniusClosedBasis
