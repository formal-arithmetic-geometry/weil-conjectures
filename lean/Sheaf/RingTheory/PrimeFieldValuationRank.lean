/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Rational rank of a valuation on a prime field

Source: Michael Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
§2.1, proof of Corollary 2.1.3(i) (blueprint: lem-trf-prime-field-valuation-rank).

Mathlib's `ValuationSubring.ValueGroup` contains an additional zero. Its unit group is
`Fˣ / Aˣ`. We write this commutative group additively before tensoring with `ℚ`.
The rational factor is placed first, using tensor symmetry, so the usual left scalar
extension supplies the `ℚ`-vector space structure.
-/

@[expose] public section

universe u

namespace ValuationSubring

/-- The value group of a valuation ring of a prime field has rational rank at most one.
Source: Temkin, *Stable modification of relative curves*, §2.1, proof of Corollary 2.1.3(i)
(blueprint: lem-trf-prime-field-valuation-rank).

The displayed disjunction expresses precisely that `F` is isomorphic to `ℚ` or to `ZMod p` for
some prime `p`. The units of `A.ValueGroup` form `Fˣ / Aˣ`; `Additive` only changes
multiplicative notation to additive notation. Tensor symmetry identifies the displayed
rationalization with `(Fˣ / Aˣ) ⊗[ℤ] ℚ`. `Module.rank` is cardinal dimension, including
infinite dimension, so the bound does not collapse the infinite-dimensional case to zero.

Proof plan (all three steps are elementary, as recorded in the DAG node):
1. Over `ZMod p`, a nonzero `x` satisfies `x^(p-1) = 1`. If only its inverse is known
   to belong to `A`, then `x = (x⁻¹)^(p-2)` also belongs; for `p = 2`, `x = 1`.
   Thus `A = F`, the quotient group is trivial, and its rational rank is zero.
2. Over `ℚ`, `A` contains `ℤ`. Its nonunits, including zero, form the maximal ideal:
   closure under multiplication follows by taking inverses, and closure under addition
   follows by applying the valuation alternative to the ratio of two nonzero summands.
   Two different rational primes cannot both lie in this ideal, since Bezout's identity
   would put `1` in it. Hence at most one rational prime is a nonunit of `A`.
3. If every rational prime is a unit, unique factorization makes the quotient trivial.
   Otherwise, unique factorization shows that the class of the unique nonunit prime
   generates the quotient. Its tensor product with `ℚ` therefore has dimension at most
   one. Transport along the field isomorphism gives the result for `F`. -/
theorem rationalRank_le_one_of_prime_field (F : Type u) [Field F]
    (hprime : Nonempty (F ≃+* ℚ) ∨
      ∃ p : ℕ, Nat.Prime p ∧ Nonempty (F ≃+* ZMod p))
    (A : ValuationSubring F) :
    Module.rank ℚ (TensorProduct ℤ ℚ (Additive A.ValueGroupˣ)) ≤ 1 := by
  sorry

end ValuationSubring
