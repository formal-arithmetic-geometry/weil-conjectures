/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q59
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Sheaf.AlgebraicGeometry.FineFanBlowup

/-!
# Integrality of monomials over a submonoid algebra

Source: ILO, Exposé VIII, 3.1.17 and Lemma 3.2.9, printed pp. 101, 104.
The coefficient argument is the supporting algebraic argument supplied in the DAG,
not a quotation of the ILO proof (blueprint: lem-trf-monomial-integrality).
-/

set_option autoImplicit false

universe u v

namespace AddMonoidAlgebra

/-- A monomial is integral over the embedded submonoid algebra precisely when a positive
multiple of its exponent lies in the submonoid. The algebra of the ambient saturation is
therefore integral over the original submonoid algebra.

Both subalgebras are ranges of the canonical maps induced by the submonoid inclusions.
The saturation uses the recorded `FineFan.saturation` through the standard
`Multiplicative` conversion, so its ambient group is exactly `G`.

Source: ILO, Exposé VIII, 3.1.17 and Lemma 3.2.9, printed pp. 101, 104; the following
supporting coefficient proof is agent supplied (blueprint: lem-trf-monomial-integrality).

Proof:
1. An integral equation is `e^(d g) + sum (i < d), a_i e^(i g) = 0`, with `d > 0`
   and each `a_i` in `k[P]`. Extract the coefficient at `d g`. It is
   `1 + sum (i < d), coeff a_i ((d-i) g) = 0`. If all positive multiples `(d-i) g`
   were outside `P`, every summand would vanish, contradicting `1 != 0` in the field.
   Thus some positive multiple of `g` is in `P`. Cancellation in `G` suffices here;
   distinct powers of `g` need not be distinct.
2. If `n > 0` and `n g` is in `P`, the monic polynomial `T^n - e^(n g)` over `k[P]`
   vanishes at `e^g`. This proves the converse by the definition of `IsIntegral`.
3. The root subset defining saturation is a submonoid: `0` belongs, and positive
   witnesses `a h` and `b h'` give the witness `ab(h+h') = b(ah) + a(bh')`.
   Each monomial of this saturation is integral by step 2. The integral closure
   (`def-weil-pbc-integral-closure`, Stacks Tag 00GO) is a subring containing `k[P]`.
   It contains the scalars, their products with these monomials, and all their finite
   sums, including the empty sum. These are exactly the elements of `k[P^sat]`.
-/
theorem monomial_integrality (k : Type u) [Field k] (G : Type v) [AddCommGroup G]
    (P : AddSubmonoid G) (g : G) :
    (IsIntegral (mapDomainAlgHom k k P.subtype).range (single g (1 : k)) ↔
      ∃ n : ℕ, 0 < n ∧ n • g ∈ P) ∧
    (∀ x : AddMonoidAlgebra k G,
      x ∈ (mapDomainAlgHom k k
        (Submonoid.toAddSubmonoid'
          (AlgebraicGeometry.FineFan.saturation P.toSubmonoid)).subtype).range →
      IsIntegral (mapDomainAlgHom k k P.subtype).range x) := by
  sorry

end AddMonoidAlgebra
