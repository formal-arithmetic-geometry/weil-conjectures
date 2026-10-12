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
# Surjectivity of the local completion comparison

Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension).
(blueprint: lem-weil-pbc-completion-tensor-local-maps-surjective)
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- Local completion tuples can be interpolated by completed tensors.
Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension),
the inverse limit of the quotient product decompositions and Tag 00MA.
(blueprint: lem-weil-pbc-completion-tensor-local-maps-surjective)

Proof:
1. Put A = R_p and B = A tensor_R S. B is finite over the Noetherian local ring A.
   The finitely many primes over m correspond to Q and have local rings S_q.
   For n > 0 the Artinian ring B/m^n B is canonically the product of the
   S_q/m^n S_q by Tags 00JA and 00CT. The isomorphisms commute with reduction
   because their maps are induced by the same localization maps at every level.
2. In each S_q the m S_q-adic and maximal-ideal-adic filtrations are cofinal:
   m S_q is contained in q S_q, and finite generation plus radical equality
   gives (q S_q)^t contained in m S_q. Tag 0394 gives the canonical comparison
   of completions, induced by the identity on S_q.
3. Given a tuple in the maximal-ideal completions, use these comparisons to
   obtain m-adic sequences in all factors. At each positive n apply the inverse
   quotient product isomorphism to their coordinates. These preimages commute
   with reduction by uniqueness, hence define an element of the m-adic
   completion of B. The n = 0 coordinate belongs to the zero quotient.
4. Tag 00MA and tensor cancellation express that element as a tensor in
   C tensor_R S. The quotient equation in the hypothesis pins down the maps on
   a tensor 1 by extensionality of completion coordinates. The S-algebra property
   then pins down the whole map by tensor induction. Its value on the tensor
   just constructed is the prescribed tuple, proving surjectivity. For empty Q
   there is one tuple in the zero product ring, and zero is its preimage. -/
theorem completion_tensor_localMaps_surjective
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
      Function.Surjective f := by sorry

end AdicCompletion
