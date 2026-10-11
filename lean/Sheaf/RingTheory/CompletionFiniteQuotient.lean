/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Completion of a finite local polynomial quotient

Source: Stacks Project, More on Algebra, Tag 07PR, degree-p step of the proof;
Algebra, Tags 07N9 and 00MA (blueprint: lem-weil-pbc-completion-finite-quotient).
-/

@[expose] public section

universe u

open Polynomial TensorProduct

namespace AdicCompletion

/-- Completion commutes with a local quotient by `X ^ p - C f`, including its tensor
presentation. Source: Stacks Project, Tag 07PR, degree-p step, using Tags 07N9 and 00MA
(blueprint: lem-weil-pbc-completion-finite-quotient).

The map `g` is specified on every quotient level: any representative `r` of the n-th
coordinate of `a` maps to the class of `φ r` at the n-th coordinate. This specifies the
completed-base action without choosing an additional algebra instance. The pure-tensor
formula specifies both the `C`-algebra and completed-base-algebra compatibilities of `γ`.

Proof:
1. The monic polynomial has degree `p ≥ 1`; its quotient is free of rank `p`, hence finite
   and integral (lem-weil-pbc-monic-quotient-free, lem-weil-pbc-finite-algebra-is-integral).
2. Integrality contracts maximal ideals to maximal ideals and makes primes over maximal
   ideals maximal. Locality therefore makes `n` the unique prime above `m`
   (lem-weil-pbc-integral-maximal-contracts-maximal,
   lem-weil-pbc-integral-prime-over-maximal-maximal).
3. Localization of a local ring at its maximal ideal is an isomorphism, since every
   denominator is a unit. It identifies the corresponding quotient systems and completions
   (lem-weil-pbc-localization-units-or-zero, def-weil-pbc-localization-at-prime).
4. Apply lem-weil-pbc-completion-finite-extension (07N9) with this unique prime, then the
   identifications in step 3. The resulting tensor comparison `γ` has the stated formula;
   the cited lemma handles the equivalence of the two adic topologies on the finite algebra.
5. Base change the one-variable, one-relation presentation, and swap the tensor factors
   (lem-weil-pbc-presentation-base-change, def-weil-pbc-mv-polynomial-ring). Compose this
   quotient identification with `γ` to obtain `θ`.
6. The two maps from `R[X]` agree on coefficients and on `X`, so they agree on every
   polynomial by the polynomial universal property (def-weil-pbc-mv-polynomial-ring). -/
theorem completion_finite_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) (hp : 1 ≤ p) (f : R) [IsLocalRing (AdjoinRoot (X ^ p - C f))] :
    let S := AdjoinRoot (X ^ p - C f)
    let m := IsLocalRing.maximalIdeal R
    let n := IsLocalRing.maximalIdeal S
    let Rhat := AdicCompletion m R
    let Shat := AdicCompletion n S
    let ι := algebraMap R Rhat
    let ιS := algebraMap S Shat
    let φ := algebraMap R S
    ∃ g : Rhat →+* Shat,
      (∀ (a : Rhat) (k : ℕ) (r : R),
        evalₐ m k a = Ideal.Quotient.mk (m ^ k) r →
        evalₐ n k (g a) = Ideal.Quotient.mk (n ^ k) (φ r)) ∧
      (∃ θ : AdjoinRoot (X ^ p - C (ι f)) ≃+* Shat,
        ∀ q : R[X],
          θ (AdjoinRoot.mk _ (Polynomial.map ι q)) = ιS (AdjoinRoot.mk _ q)) ∧
      (∃ γ : (Rhat ⊗[R] S) ≃+* Shat,
        ∀ (a : Rhat) (c : S), γ (a ⊗ₜ[R] c) = g a * ιS c) := by
  sorry

end AdicCompletion
