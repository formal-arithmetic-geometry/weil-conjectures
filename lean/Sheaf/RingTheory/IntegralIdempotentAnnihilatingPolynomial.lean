/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Group.Idempotent

/-!
# An annihilating polynomial for an integral lift of an idempotent

Source: Stacks Project, More on Algebra, Lemma Tag 09XG (lemma-helper-integral)
(blueprint: lem-weil-pbc-integral-idempotent-annihilating-polynomial).
-/

universe u v

namespace Polynomial

/-- An element of an integral algebra that is idempotent modulo the extended ideal has
an annihilating monic polynomial reducing to `X ^ d * (X - 1) ^ d` for some `d ≥ 1`.
Source: Stacks Project, More on Algebra, Lemma Tag 09XG (lemma-helper-integral).
(blueprint: lem-weil-pbc-integral-idempotent-annihilating-polynomial)

Proof: First put `z = b² - b`. Idempotence in the quotient says that `z` belongs to `IB`.
Apply `lem-weil-pbc-integral-extended-ideal-element-monic` (Stacks Tag 00H5, Mathlib's
`Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map`) to obtain a monic `g`
annihilating `z`, with all non-leading coefficients in `I`. If its degree is zero,
then `g = 1` and `B` is the zero ring; replace `g` by `X * g` to obtain degree one.
Thus its degree `d` is positive. Put `f = g.comp (X² - X)`. Composition of monic
polynomials makes `f` monic, and evaluation gives `f(b) = g(z) = 0`. Reducing
coefficients modulo `I` commutes with composition and kills the non-leading
coefficients of `g`, giving `(X² - X)^d = X^d * (X - 1)^d`. -/
theorem exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (I : Ideal A) (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A B)) b)) :
    ∃ (d : ℕ) (f : A[X]), 1 ≤ d ∧ f.Monic ∧ aeval b f = 0 ∧
      f.map (Ideal.Quotient.mk I) = (X : (A ⧸ I)[X]) ^ d * (X - 1) ^ d := by
  sorry

end Polynomial
