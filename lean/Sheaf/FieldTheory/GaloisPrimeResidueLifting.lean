/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic

/-!
# Prime transitivity and residue automorphism lifting in a Galois integral closure

Source: Stacks Project, More on Algebra, Tag 0BRK,
`lemma-one-orbit-geometric-galois`, part (1) and the surjectivity clause of part (2).
(blueprint: lem-dl-a1-galois-prime-residue-lifting)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped Pointwise

namespace Ideal

/-- The Galois group acts transitively on primes of the integral closure with equal
contraction, and the stabilizer of each prime realizes every automorphism of its residue
field over the contracted residue field. Here `s.ResidueField` is canonically a fraction
field of the domain `integralClosure R E ⧸ s`. A residue-field automorphism over the base
is written as a ring equivalence commuting with the canonical embedding
`Ideal.ResidueField.map`. Its induced action is specified on the images of all integral
elements; those images generate the residue fraction field, so this specifies the action
on the entire field uniquely.

Source: Stacks Project, More on Algebra, Tag 0BRK,
`lemma-one-orbit-geometric-galois`, part (1) and the surjectivity clause of part (2).
(blueprint: lem-dl-a1-galois-prime-residue-lifting)

Proof:
1. Equip `E ≃ₐ[F] E` with the Krull topology. By
   `lem-exc-galois-krull-finite-limit` it is the inverse limit of the finite discrete
   Galois groups of finite Galois intermediate fields. Their indexing poset is nonempty,
   set-sized and directed. By `lem-dl-a1-finite-group-limit-profinite`, the group is
   compact Hausdorff and totally disconnected. Fixing finitely many elements is open.
2. Each automorphism preserves the integral closure by applying it to monic equations
   over R, and its inverse gives the inverse restriction. With the integral closure
   discrete, every orbit map is locally constant: fibers are cosets of open stabilizers.
   Checking on the open slices of the product gives a continuous action. It fixes R.
   Conversely, an integral element fixed by the group lies in F by
   `lem-exc-etale-galois-fixed-field-subgroup`, applied to the bottom intermediate field.
   Since R is a normal domain, that element lies in R. Thus the invariant ring is R.
3. Apply the prime-transitivity clause of `lem-dl-a1-profinite-invariant-ring-primes`
   to this action to obtain the first conjunct.
4. For a prime s with contraction p, localize R and its integral closure at R minus p,
   obtaining subrings A of F and B of E. The map sending b/t to its residue fraction
   has prime kernel Q, contracting to s; its contraction to A is P = pA. Extend the
   action by g(b/t) = g(b)/t. This action is continuous on discrete B because each
   numerator has open stabilizer. Cancellation shows that a fixed b/t has fixed
   numerator b, hence b lies in R by step 2. Thus the invariant ring of B is A.
5. By `lem-weil-pbc-localization-quotient-by-prime`, A/P is the fraction field of R/p,
   while B/Q is the localization of the original quotient by the image of R minus p.
   By the integrality clause of `lem-dl-a1-profinite-invariant-ring-primes`, B is
   integral over A, so B/Q is integral over the field A/P. This domain is a field:
   a monic relation of least degree for a nonzero element has nonzero constant term
   (otherwise cancel that element), and rearranging gives its inverse. The natural
   injection from B/Q into the fraction field of the original quotient is surjective,
   since its field image contains the original quotient and therefore its fractions.
   All these identifications respect the base embedding and the displayed fractions.
6. Transport the prescribed residue automorphism to an A/P-algebra automorphism of B/Q.
   The quotient-lifting clause of `lem-dl-a1-profinite-invariant-ring-primes` supplies
   g stabilizing Q and inducing this automorphism. Contracting Q back to the integral
   closure shows that g stabilizes s. The formula on b/t is the residue of g(b)/t;
   hence g induces the prescribed automorphism on the entire residue fraction field,
   giving the second conjunct. -/
theorem galois_prime_transitivity_and_residue_lifting
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (E : Type w) [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [IsGalois F E] :
    (∀ (s s' : Ideal (integralClosure R E)) [s.IsPrime] [s'.IsPrime],
      s.under R = s'.under R → ∃ g : E ≃ₐ[F] E, g • s = s') ∧
    (∀ (s : Ideal (integralClosure R E)) [s.IsPrime]
      (α : s.ResidueField ≃+* s.ResidueField),
      α.toRingHom.comp
          (Ideal.ResidueField.map (s.under R) s (algebraMap R (integralClosure R E)) rfl) =
        Ideal.ResidueField.map (s.under R) s (algebraMap R (integralClosure R E)) rfl →
      ∃ g : E ≃ₐ[F] E, g • s = s ∧
        ∀ b : integralClosure R E,
          α (algebraMap (integralClosure R E) s.ResidueField b) =
            algebraMap (integralClosure R E) s.ResidueField (g • b)) := by
  sorry

end Ideal
