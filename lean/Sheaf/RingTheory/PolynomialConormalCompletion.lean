/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.Order
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completion of a polynomial presentation and its conormal differential

Source: Stacks Project, restricted.tex, Tag 0GAF (lemma-NL-is-completion) and
Equation (equation-NL) (blueprint: lem-per-polynomial-conormal-completion).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Completing a polynomial presentation preserves the conormal module and its differential.
Source: Stacks Project, Tag 0GAF and Equation (equation-NL).
(blueprint: lem-per-polynomial-conormal-completion).

The completion homomorphism and the completed partial derivatives are specified on every
quotient coordinate. The topology is the inverse-limit topology with discrete quotients.
`Extension.Cotangent` is the kernel modulo its square, with its quotient-ring module action.
The completion tensor factor is written on the left; `TensorProduct.comm` gives the displayed
right-factor convention of the node. Both equivalences below are linear over the completion.

Proof:
1. The finite polynomial algebra is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. Put L = IS. The modules S, B, K, K² and
   K/K² are finite over S; completion at L agrees with completion at the base ideal I.
2. Complete 0 → K → S → B → 0 using lem-weil-pbc-completion-exact-finite-modules.
   By lem-weil-pbc-completion-finite-module-tensor, the completed kernel has image KP.
   Thus the coordinatewise completed map is onto with kernel J = KP.
3. Complete 0 → K² → K → K/K² → 0. Exactness and the same tensor comparison identify
   the completed conormal with J/J², since K²P = (KP)² by expansion of products.
4. The tensor balancing relations of def-weil-pbc-module-tensor-product identify this
   completion with the scalar extension over B: a lift of b in the completed S can be
   changed by an element of J, which acts trivially on K/K². The isomorphism sends
   b ⊗ [k] to b[k].
5. Each polynomial partial derivative is A-linear and preserves IⁿS. It therefore descends
   to each quotient and commutes with transition maps. Apply it coordinatewise to obtain
   the completed derivative. Preservation of coordinate kernels proves continuity.
6. The product rule of def-weil-pbc-polynomial-partial-derivative kills K² after applying
   α, and kills J² after applying its completion. The same rule proves B-linearity and
   completed-B-linearity of the two conormal differentials, respectively.
7. The finite free-module comparison sends b ⊗ v to (b vᵢ)ᵢ; its inverse uses the finite
   sum of standard basis vectors. On b ⊗ [k], the completed product rule gives precisely
   b times the completed image of α(∂ᵢk). Pure tensors generate, proving the asserted
   equality of differentials, also for r = 0. -/
theorem polynomial_conormal_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (r : ℕ)
    (B : Type v) [CommRing B] [Algebra A B]
    (α : MvPolynomial (Fin r) A →ₐ[A] B) (hα : Function.Surjective α)
    (_hK : (RingHom.ker α.toRingHom).FG) :
    ∃ αhat : AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
        (MvPolynomial (Fin r) A) →ₐ[A] AdicCompletion (I.map (algebraMap A B)) B,
      (∀ (n : ℕ)
          (p : AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
            (MvPolynomial (Fin r) A)) (f : MvPolynomial (Fin r) A),
        AdicCompletion.evalₐ _ n p = Ideal.Quotient.mk (_ ^ n) f →
        AdicCompletion.evalₐ _ n (αhat p) = Ideal.Quotient.mk (_ ^ n) (α f)) ∧
      ∃ hαhat : Function.Surjective αhat,
        RingHom.ker αhat.toRingHom =
          (RingHom.ker α.toRingHom).map
            (algebraMap (MvPolynomial (Fin r) A)
              (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
                (MvPolynomial (Fin r) A))) ∧
        ∃ D : Fin r →
            AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
              (MvPolynomial (Fin r) A) →ₗ[A]
            AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
              (MvPolynomial (Fin r) A),
          (∀ (i : Fin r) (n : ℕ)
              (p : AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
                (MvPolynomial (Fin r) A)) (f : MvPolynomial (Fin r) A),
            AdicCompletion.evalₐ _ n p = Ideal.Quotient.mk (_ ^ n) f →
            AdicCompletion.evalₐ _ n (D i p) =
              Ideal.Quotient.mk (_ ^ n) (MvPolynomial.pderiv i f)) ∧
          (∀ i : Fin r, @Continuous _ _
            (⨅ n : ℕ, TopologicalSpace.induced
              (AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial (Fin r) A))) n) ⊥)
            (⨅ n : ℕ, TopologicalSpace.induced
              (AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial (Fin r) A))) n) ⊥)
            (D i)) ∧
          ∃ e : (AdicCompletion (I.map (algebraMap A B)) B ⊗[B]
              (Extension.ofSurjective α hα).Cotangent) ≃ₗ[
                AdicCompletion (I.map (algebraMap A B)) B]
              (Extension.ofSurjective αhat hαhat).Cotangent,
            (∀ (k : (Extension.ofSurjective α hα).ker)
                (q : (Extension.ofSurjective αhat hαhat).ker),
              (q.val : AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
                (MvPolynomial (Fin r) A)) =
                  algebraMap (MvPolynomial (Fin r) A)
                    (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
                      (MvPolynomial (Fin r) A)) k.val →
              ∀ b : AdicCompletion (I.map (algebraMap A B)) B,
                e (b ⊗ₜ[B] Extension.Cotangent.mk k) = b • Extension.Cotangent.mk q) ∧
            ∃ (d₀ : (Extension.ofSurjective α hα).Cotangent →ₗ[B] (Fin r → B))
              (dhat : (Extension.ofSurjective αhat hαhat).Cotangent →ₗ[
                AdicCompletion (I.map (algebraMap A B)) B]
                (Fin r → AdicCompletion (I.map (algebraMap A B)) B)),
              (∀ (k : (Extension.ofSurjective α hα).ker) (i : Fin r),
                d₀ (Extension.Cotangent.mk k) i = α (MvPolynomial.pderiv i k.val)) ∧
              (∀ (q : (Extension.ofSurjective αhat hαhat).ker) (i : Fin r),
                dhat (Extension.Cotangent.mk q) i = αhat (D i q.val)) ∧
              ∃ t : (AdicCompletion (I.map (algebraMap A B)) B ⊗[B] (Fin r → B)) ≃ₗ[
                  AdicCompletion (I.map (algebraMap A B)) B]
                  (Fin r → AdicCompletion (I.map (algebraMap A B)) B),
                (∀ (b : AdicCompletion (I.map (algebraMap A B)) B)
                    (w : Fin r → B) (i : Fin r),
                  t (b ⊗ₜ[B] w) i = b * algebraMap B _ (w i)) ∧
                ∀ z, dhat (e z) = t (LinearMap.lTensor _ d₀ z) := by
  sorry

end Algebra
