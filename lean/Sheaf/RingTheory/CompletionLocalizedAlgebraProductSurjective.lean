/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.FiniteAfterCompletion
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Interpolation in the completion of a localized finite algebra

Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension),
the second equality, before the use of Tag 00MA.
(blueprint: lem-weil-pbc-completion-localized-algebra-product-surjective)
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The completion of the localized algebra maps onto its local completion product.
Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension),
second equality; Tag 0394 (lemma-finite-after-completion).
(blueprint: lem-weil-pbc-completion-localized-algebra-product-surjective)

Proof:
1. Write A = R_p, m = pA, B = A tensor_R S, and J = pB = mB. The ring A is
   Noetherian local, and B is finite over A. Localization identifies the primes
   of B above m with Q, and their local rings with S_q. The stipulated maps psi
   are these localization maps: their values on A and S fix them on pure tensors.
2. For every positive n, B/J^n is Artinian. Its primes correspond to Q. The
   product-of-localizations theorem and localization of quotients identify
   B/J^n with the product of S_q/(J S_q)^n. The identifications commute with
   reduction since their coordinates are induced by the same maps psi.
3. Each S_q is Noetherian local, with finite-dimensional special fibre over A/m.
   Tag 0394 identifies its maximal-ideal completion with its J S_q-adic
   completion, via the identity on representatives. Given a tuple y, take its
   preimage under these canonical comparisons. For each positive n, use the
   inverse of the product quotient isomorphism to lift its coordinates to
   B/J^n. Uniqueness of these lifts and compatibility of the quotient maps show
   they form a compatible sequence. At n = 0 use the unique element of B/(1).
4. This sequence defines x in AdicCompletion J B. The level formula for g shows
   that g x = y at every coordinate and every level, by the comparisons in step 3.
   Completion extensionality gives equality. If Q is empty, its product is the
   zero ring and g is surjective with preimage zero.

This statement concerns only inverse limits of the localized algebra. It does
not identify that completion with a tensor product of the completed base. -/
theorem completion_localizedAlgebra_product_surjective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    ∀ (ψ : ∀ q : Q, B →ₐ[S] Localization.AtPrime q.1),
      (∀ (q : Q) (r : A), ψ q (r ⊗ₜ[R] (1 : S)) =
        Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p)) r) →
      ∀ (g : AdicCompletion J B →+* (∀ q : Q, D q)),
        (∀ (q : Q) (n : ℕ) (x : AdicCompletion J B) (b : B),
          evalₐ J n x = Ideal.Quotient.mk (J ^ n) b →
          evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n (g x q) =
            Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n) (ψ q b)) →
        Function.Surjective g := by sorry

end AdicCompletion
