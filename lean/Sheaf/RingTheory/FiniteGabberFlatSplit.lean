/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
import Sheaf.RingTheory.LiftIdempotentUpstairs

/-!
# The flat split neighbourhood in Gabber's finite-algebra argument

Source: Stacks Project, More on Algebra, Tag 0EM0, proof of `lemma-helper-finite`,
from lifting the idempotent through choosing the coefficient in the first factor.
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- A flat neighbourhood preserving the quotient splits the finite algebra into two
factors. The first factor admits a scalar lift of `b - 1`, and `b` in the second factor
belongs to the extended ideal. The kernels of the two factor projections have zero
intersection. No polynomial relation or faithful flatness is asserted here.
Source: Stacks Project, More on Algebra, Tag 0EM0, proof of `lemma-helper-finite`.
(blueprint: lem-weil-pbc-gabber-flat-split-neighbourhood)

Proof:
1. Finiteness makes B integral. Apply 07M4 to the idempotent represented by b
   modulo IB. This gives an etale A-algebra A' preserving A/I, and an idempotent
   in B tensor_A A' reducing to (1,0).
2. The idempotent decomposes the tensor algebra into its quotient by (1-e') and
   its quotient by e'. Both factors are finite over A'. Their reductions are B1
   and B2, and the image of b reduces respectively to 1 and 0.
3. The cokernel of A' -> the first factor is finite and equals IA' times itself,
   because A/I -> B1 is surjective. Nakayama 00DV gives g with g-1 in IA' which
   annihilates this cokernel. Localize A' and both factors at g to obtain C.
4. C is flat over A: etale algebras and localizations are flat, and flatness
   composes. Since g reduces to 1, A/I -> C/IC is still an isomorphism, agreeing
   with the structure map on representatives.
5. The first structure map is now surjective: y/g^n is the image of a/g^(n+1)
   whenever gy is the image of a. Its extended ideal is therefore the image of
   IC, so lift the first component of b-1 to a in IC. Let K and L be the kernels
   of the two factor projections from C tensor_A B. Their intersection is zero.
   The first equality says b-1-a belongs to K. The second component of b is in
   IC times that factor, equivalently b belongs to L plus the extended ideal.
   These conclusions also hold when either factor is the zero ring. -/
theorem exists_flat_split_gabber_neighbourhood
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (C : CommRingCat.{u}) (f : A →+* C),
      letI : Algebra A C := f.toAlgebra
      Module.Flat A C ∧
        ∃ α : A ⧸ I ≃+* C ⧸ I.map (algebraMap A C),
          (∀ a : A, α (Ideal.Quotient.mk I a) =
            Ideal.Quotient.mk _ (algebraMap A C a)) ∧
          ∃ K L : Ideal (TensorProduct A C B), K ⊓ L = ⊥ ∧
            ∃ a : C, a ∈ I.map (algebraMap A C) ∧
              ((1 : C) ⊗ₜ[A] b) - 1 - algebraMap C (TensorProduct A C B) a ∈ K ∧
              ((1 : C) ⊗ₜ[A] b) ∈ L ⊔
                (I.map (algebraMap A C)).map (algebraMap C (TensorProduct A C B)) := by
  sorry

end Algebra
