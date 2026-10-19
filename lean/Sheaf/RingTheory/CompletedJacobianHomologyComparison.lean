/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.RingTheory.CompletedPolynomialConormal
public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.RingTheory.FiniteType

/-!
# Completed Jacobian homology comparison

Source: Stacks Project, restricted.tex, Tags 0GAF and 0GAE
(blueprint: lem-per-completed-jacobian-homology-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

/-- The ordinary and continuous conormal arrows, specified on every conormal class,
have the same homology after completion. The existential arrows are uniquely determined
by the displayed formulas; no choice of an unrelated differential is allowed.
Source: Stacks Project, restricted.tex, Tags 0GAF and 0GAE
(blueprint: lem-per-completed-jacobian-homology-comparison).

Proof:
1. By lem-weil-pbc-finite-type-algebra-noetherian the polynomial algebra and C are
Noetherian. Its finitely generated kernel gives a finite conormal module. Its image,
cokernel and kernel are finite, the last by lem-weil-pbc-noetherian-submodule-finite.
2. By lem-weil-pbc-adic-completion-mod-ideal the completed C is complete and its reduction
modulo I is C/IC, finite type over A/I.
3. By lem-per-polynomial-conormal-completion the completed ordinary presentation is
surjective and its conormal arrow is the base change of the ordinary arrow. By
lem-weil-pbc-completion-finite-module-tensor this is its completed arrow, naturally.
The completion of the finite coordinate module is the coordinate module of the completion.
4. Apply lem-weil-pbc-completion-exact-finite-modules to the two short exact sequences
through the image of the ordinary differential. This identifies its completed kernel and
cokernel with the kernel and cokernel of the completed arrow.
5. Apply the presentation-independence clause of lem-per-completed-cotangent-transitivity
to the completed ordinary presentation and beta, using Step 2. Every A-algebra map beta
preserves I powers, so no additional continuity assumption is needed.
6. The resulting homotopy inverses induce inverse maps on kernels and cokernels:
a homotopy changes a map by hd in degree -1 and dh in degree 0, both zero on homology.
Compose with Step 4. The formulas for the arrows follow from polynomial differentiation
and its continuous extension, which kill the square of the respective kernel. -/
theorem completedJacobianHomologyComparison
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {C : Type v} [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (s r : ℕ) (α : MvPolynomial (Fin s) A →ₐ[A] C)
    (hα : Function.Surjective α)
    (β : rigPolynomialCompletion I r →ₐ[A]
      AdicCompletion (I.map (algebraMap A C)) C)
    (hβ : Function.Surjective β) :
    ∃ (dα : (Algebra.Extension.ofSurjective α hα).Cotangent →ₗ[C] (Fin s → C))
      (dβ : (Algebra.Extension.ofSurjective β hβ).Cotangent →ₗ[
        AdicCompletion (I.map (algebraMap A C)) C]
        (Fin r → AdicCompletion (I.map (algebraMap A C)) C)),
      (∀ (f : RingHom.ker α.toRingHom) (j : Fin s),
        dα (Algebra.Extension.Cotangent.mk f) j = α (MvPolynomial.pderiv j f.val)) ∧
      (∀ (f : RingHom.ker β.toRingHom) (j : Fin r),
        dβ (Algebra.Extension.Cotangent.mk f) j = β (rigPartialDerivative I r j f.val)) ∧
      Nonempty (AdicCompletion (I.map (algebraMap A C)) dα.ker ≃ₗ[
        AdicCompletion (I.map (algebraMap A C)) C] dβ.ker) ∧
      Nonempty (AdicCompletion (I.map (algebraMap A C)) ((Fin s → C) ⧸ dα.range) ≃ₗ[
        AdicCompletion (I.map (algebraMap A C)) C]
          ((Fin r → AdicCompletion (I.map (algebraMap A C)) C) ⧸ dβ.range)) := by
  sorry

end AlgebraicGeometry
