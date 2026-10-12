/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.RingTheory.FiniteAfterCompletion
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Injectivity of the local completion comparison

Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension).
(blueprint: lem-weil-pbc-completion-tensor-local-maps-injective)
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- Local completion maps detect equality of completed tensors.
Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension),
the quotient product decomposition and the final application of Tag 00MA.
(blueprint: lem-weil-pbc-completion-tensor-local-maps-injective)

Proof:
1. Put A = R_p and B = A tensor_R S. B is finite over the Noetherian local ring A.
   Localization identifies the primes of B over its maximal ideal m with Q, and
   their local rings with S_q. Every B/m^n B for n > 0 is Artinian. Its canonical
   map to the product of S_q/m^n S_q is an isomorphism by Tags 00JA and 00CT.
2. These canonical maps commute with reduction. Thus the map from the m-adic
   completion of B into the product of the m-adic completions of S_q is injective:
   if every component is zero, each quotient coordinate is zero by the quotient
   product isomorphism, and the original compatible sequence is zero.
3. In S_q, the extended ideal m S_q has radical q S_q. Noetherianity gives a
   power of q S_q contained in m S_q; the converse inclusion is immediate.
   Tag 0394 identifies the two completions by the identity on S_q. Therefore
   replacing the factors by the maximal-ideal completions preserves injectivity.
4. Tag 00MA identifies C tensor_A B with the m-adic completion of B, and tensor
   cancellation identifies C tensor_A B with C tensor_R S. Under this canonical
   comparison the resulting map sends a tensor s to the tuple g_q(a) times s.
   The hypothesis on f determines g_q: choose a representative of each quotient
   coordinate of a and apply the displayed equation, then use extensionality of
   compatible sequences. S-linearity and tensor induction identify f with this
   comparison map. Composing the injections proves the claim. The zero algebra
   and empty Q are included: B/m^n B and its completion are then zero. -/
theorem completion_tensor_localMaps_injective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    ∀ (f : (C ⊗[R] S) →ₐ[S] (∀ q : Q, D q)),
      (∀ (q : Q) (n : ℕ) (a : C) (r : A),
        evalₐ m n a = Ideal.Quotient.mk (m ^ n) r →
        evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n
            (f (a ⊗ₜ[R] (1 : S)) q) =
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
            (Localization.localRingHom p q.1 (algebraMap R S)
              (Ideal.LiesOver.over (P := q.1) (p := p)) r)) →
      Function.Injective f := by sorry

end AdicCompletion
