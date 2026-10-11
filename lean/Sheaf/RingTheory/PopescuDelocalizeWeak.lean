/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.PopescuResolution
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Weak delocalization of a Popescu resolution

Source: Stacks Project, Smoothing Ring Maps, Lemma 07F9
(blueprint: lem-weil-pbc-popescu-delocalize-weak).
-/

@[expose] public section

universe u v t

namespace Algebra

/-- A resolution after localization at a minimal prime over the extended singular ideal
can be delocalized to a finitely presented factorization whose extended singular ideal
escapes that prime. Source: Stacks Project, Smoothing Ring Maps, Lemma 07F9
(blueprint: lem-weil-pbc-popescu-delocalize-weak).

Proof (the node's fourteen steps):
1. In the local target, the resolving algebra's extended singular ideal is the unit ideal,
   by `def-weil-pbc-popescu-resolution`, `def-weil-pbc-singular-ideal`, and
   `def-weil-pbc-localization-at-prime`.
2. Apply `lem-weil-pbc-popescu-final-solve` (07EU) to factor through a smooth algebra.
3. Use `lem-weil-pbc-smooth-retract-standard-smooth` (07CH) and reroute the factorization
   through the standard smooth algebra using its section and retraction.
4. Present A by finitely many generators and relations and record their images in Λ.
5. By `lem-weil-pbc-standard-smooth-include-generators` (07EY), choose a standard smooth
   presentation including those generators and with invertible Jacobian determinant.
6. Identify the polynomial ring over R_p as a localization using
   `lem-weil-pbc-polynomial-scalar-extension` and `lem-weil-pbc-localization-base-change`.
7. Clear denominators of the defining equations; the determinant changes by a unit.
8. Clear a relation expressing the inverse determinant to obtain s₀ outside p.
9. Clear the relations of A to obtain sⱼ outside p annihilating them modulo the equations.
10. Choose one common denominator outside q for the extra generators' images in Λ_q.
11. Homogenize the equations in the extra variables and clear their vanishing in Λ_q
    with one element λ₀ outside q, using the fraction description of localization.
12. Form B with the relations of A and λ₀ times the homogenized equations. Evaluation
    gives maps A → B → Λ with composite α.
13. Apply `lem-weil-pbc-popescu-delocalize-weak-localization-smooth` to the product b
    of the homogenizing variables and the sⱼ to see that B_b is smooth over R.
14. Hence b belongs to `singularIdeal R B`; its image is a product of elements outside q.
    This proves the asserted noncontainment. The minimal-prime hypothesis is retained,
    though the node's proof observes that it is unused.

The localized algebra is the base change R_p ⊗[R] A (canonically A ⊗[R] R_p), and the
induced map A_p → Λ_q is `Algebra.TensorProduct.lift` of the structure map R_p → Λ_q and α
followed by Λ → Λ_q, as in the sibling
lem-weil-pbc-popescu-delocalize-height-zero. The local algebra structure on Λ_q is the
canonical one, and qΛ_q is the maximal ideal of Λ_q.
-/
theorem exists_factorization_singularIdeal_not_le_of_local_popescu_resolution
    {R : Type u} {A : Type v} {Λ : Type t}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)
    (hlocal :
      letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
      CanBePopescuResolved
        (Algebra.TensorProduct.lift
          (Algebra.ofId (Localization.AtPrime (q.asIdeal.under R))
            (Localization.AtPrime q.asIdeal))
          ((IsScalarTower.toAlgHom R Λ (Localization.AtPrime q.asIdeal)).comp α)
          (fun _ _ => Commute.all _ _))
        ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal), inferInstance⟩) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C),
      ∃ (β : A →ₐ[R] C) (γ : C →ₐ[R] Λ),
        FinitePresentation R C ∧ γ.comp β = α ∧
          ¬ Ideal.map γ.toRingHom (singularIdeal R C) ≤ q.asIdeal := by
  sorry

end Algebra
