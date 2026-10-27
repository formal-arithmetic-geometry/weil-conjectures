/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.TensorProduct.Maps

import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange

/-! # Polynomial power lifting gives a universal homeomorphism

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Remark 3.2.2, Lemma 3.1.4 and the implication (2) => (1) of Proposition 3.3.5;
Stacks Project, Tags 0BR8, 00FI and 00E0
(blueprint: lem-sfb-polynomial-power-lifting-universal-homeomorphism).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace PrimeSpectrum

/-- An injective ring map admitting positive-power lifts on every finite polynomial
extension induces a homeomorphism on spectra after every commutative algebra base change.
The ring map is encoded by the arbitrary algebra structure `Algebra R B`.

Source: Alper, Remark 3.2.2, Lemma 3.1.4 and Proposition 3.3.5 (2) => (1);
Stacks Project, Tags 0BR8, 00FI and 00E0
(blueprint: lem-sfb-polynomial-power-lifting-universal-homeomorphism).

Proof:
1. Use the power-lifting hypothesis with zero variables, identifying the polynomial
   rings with their coefficient rings (def-weil-pbc-mv-polynomial-ring). Injectivity
   makes the kernel zero. Apply lem-pur-all-element-powers-spectrum-homeomorphism
   to obtain a homeomorphism Spec B -> Spec R, hence a surjection.
2. For an arbitrary R-algebra C, set D = C tensor_R B and g(c) = c tensor 1.
   The ring structure and inclusions come from
   lem-weil-pbc-algebra-tensor-pushout-universal-property. Apply
   lem-weil-pbc-spec-surjective-base-change to obtain surjectivity of Spec g.
3. Write z in D as a finite sum of c_j tensor b_j using
   def-weil-pbc-module-tensor-product. Apply the hypothesis to the polynomial
   P = sum b_j t_j to obtain a positive N and A with map(A) = P^N.
   Evaluate coefficients b at 1 tensor b and variables t_j at c_j tensor 1.
   Polynomial evaluation (def-weil-pbc-mv-polynomial-ring) and tensor balancing
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) give
   z^N = g(A(c_1,...,c_m)). For the empty sum use A = 0 and N = 1.
4. If g(c) = 0, surjectivity of Spec g puts c in every prime of C. By
   lem-weil-pbc-zero-locus-eq-iff-radical-eq, c is in the radical of the zero
   ideal, hence nilpotent. Only elementwise nilpotence is needed.
5. Apply lem-pur-all-element-powers-spectrum-homeomorphism to g using steps
   3 and 4. Its conclusion is the required homeomorphism of Zariski spaces. -/
theorem isHomeomorph_comap_includeLeft_of_polynomial_power_lifting
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (hf : Function.Injective (algebraMap R B))
    (hpow : ∀ (n : ℕ) (b : MvPolynomial (Fin n) B),
      ∃ N : ℕ, 0 < N ∧ ∃ a : MvPolynomial (Fin n) R,
        MvPolynomial.map (algebraMap R B) a = b ^ N)
    (C : Type w) [CommRing C] [Algebra R C] :
    IsHomeomorph (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[R] B)) := by
  sorry

end PrimeSpectrum
