/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.Ideal.Operations
import Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange

/-!
# Polynomial tests for power lifting after arbitrary base change

Source: Alper, Adequate moduli spaces, Remark 3.2.2, printed p.496; Lemma 3.1.4,
printed p.495; spectral argument of Proposition 3.3.5, printed p.498
(blueprint: lem-sfb-polynomial-adequacy-nil-base-change).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Finite polynomial power lifting and an elementwise nilpotent kernel imply the same
properties after every commutative algebra base change. The given ring map is
`algebraMap R S`; an arbitrary ring homomorphism supplies this algebra structure.
The tensor ring and its left inclusion are Mathlib's canonical constructions.

Source: Alper, Adequate moduli spaces, Remark 3.2.2, printed p.496; Lemma 3.1.4,
printed p.495; spectral argument of Proposition 3.3.5, printed p.498
(blueprint: lem-sfb-polynomial-adequacy-nil-base-change).

Proof:
1. Apply the polynomial hypothesis with zero variables. Every element of `S` has
   a positive power in the image of `R`. Together with `hker`,
   `lem-pur-all-element-powers-spectrum-homeomorphism`
   (`PrimeSpectrum.isHomeomorph_comap`) makes `Spec S -> Spec R` a homeomorphism.
2. For `D = E ⊗[R] S`, the tensor ring, its multiplication and both inclusions are
   those of `lem-weil-pbc-algebra-tensor-pushout-universal-property` (1).
   By `lem-weil-pbc-spec-surjective-base-change`, `Spec D -> Spec E` is surjective.
3. A kernel element belongs to every prime ideal of `E`, by lifting that prime
   along the surjection. Apply `lem-weil-pbc-zero-locus-eq-iff-radical-eq` to the
   zero ideal: the intersection of all primes is its radical. Thus each kernel
   element is nilpotent, without a common exponent for the whole kernel.
4. By `def-weil-pbc-module-tensor-product`, write `z = sum_i e_i ⊗ s_i` as a finite
   sum. Apply `hpoly` to `b = sum_i s_i * X_i`. Evaluate the lifted polynomial at
   the images of the `e_i` in `D`, with coefficients mapped by the right inclusion.
   Tensor balancing identifies the coefficient maps from `R`; the evaluation
   uniqueness of `def-weil-pbc-mv-polynomial-ring` identifies the whole maps.
   The evaluated equality is `z ^ N = includeLeftRingHom (a(e_i))`. Multiplication
   on pure tensors is `(e ⊗ s) * (e' ⊗ s') = (e * e') ⊗ (s * s')`.
   For the empty sum, `z = 0`, and exponent one and preimage zero suffice. -/
theorem nil_kernel_and_power_lifting_baseChange_of_polynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hker : ∀ r : R, algebraMap R S r = 0 → IsNilpotent r)
    (hpoly : ∀ (n : ℕ) (b : MvPolynomial (Fin n) S),
      ∃ N : ℕ, 0 < N ∧ ∃ a : MvPolynomial (Fin n) R,
        MvPolynomial.map (algebraMap R S) a = b ^ N)
    (E : Type w) [CommRing E] [Algebra R E] :
    (∀ e : E,
      (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[R] S) e = 0 →
        IsNilpotent e) ∧
    (∀ z : E ⊗[R] S, ∃ M : ℕ, 0 < M ∧ ∃ e : E,
      (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[R] S) e = z ^ M) := by
  sorry

end Algebra
