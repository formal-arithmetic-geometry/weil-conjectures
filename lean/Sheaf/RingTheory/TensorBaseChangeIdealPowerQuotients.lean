/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Tensor base change and ideal-power quotients

Source: Stacks Project, algebra.tex, Tag 00CX (lemma-tensor-product), and the
finite-level scalar-congruence quotient calculation in the DAG proof
(blueprint: lem-trf-tensor-base-change-ideal-power-quotients).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- A scalar congruence modulo `I ^ n` identifies the quotients after tensor base change
by every ideal `J` containing the extended ideal `I`. The representative identities
characterize both the canonical equivalence and the induced scalar map uniquely.

Source: Stacks Project, algebra.tex, Tag 00CX (lemma-tensor-product), with the explicit
finite-level scalar-congruence quotient argument recorded in the DAG
(blueprint: lem-trf-tensor-base-change-ideal-power-quotients).

Proof:
1. Put K = J^n and E = C/K. Since the image of I is contained in J, the image of I^n
   is contained in K. Thus rhoBar([r]) = [algebraMap R C r] is a well-defined ring map.
2. Compose rhoBar with pi. By the tensor-algebra universal property
   (lem-weil-pbc-algebra-tensor-pushout-universal-property), the quotient map C -> E
   and this composite induce h : C tensor_R B -> E with h(c tensor b) = [c]rhoBar(pi(b)).
   Its restriction along c -> c tensor 1 is the quotient map C -> E.
3. The map h kills the extended ideal K, so it descends to beta : D/KD -> E.
   Conversely c -> c tensor 1 induces alpha : E -> D/KD, since it sends K into KD.
4. For b in B, choose r representing pi(b). The difference b - algebraMap R B r lies
   in ker(pi) = I^n B. Express it as a finite sum of products of images of elements
   of I^n and elements of B. Balancing shows c tensor (b - algebraMap R B r) lies
   in KD. Hence [c tensor b] = alpha([c * algebraMap R C r]).
5. The composite beta alpha is the identity on quotient representatives. Step 4 shows
   alpha beta is the identity on pure tensor classes, hence on all classes by their
   additive generation (def-weil-pbc-module-tensor-product). These mutually inverse
   ring maps give e. The formula from step 2 is the asserted formula for e.symm.
-/
theorem tensor_base_change_ideal_power_quotients
    {R : Type u} {B : Type v} {C : Type w}
    [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (I : Ideal R) (J : Ideal C) (hIC : I.map (algebraMap R C) ≤ J)
    (n : ℕ) (hn : 1 ≤ n) (π : B →ₐ[R] R ⧸ I ^ n)
    (hπ : Function.Surjective π)
    (hker : RingHom.ker π.toRingHom = (I ^ n).map (algebraMap R B)) :
    ∃ (e : (C ⧸ J ^ n) ≃+*
        ((C ⊗[R] B) ⧸ (J ^ n).map (algebraMap C (C ⊗[R] B))))
      (rhoBar : (R ⧸ I ^ n) →+* (C ⧸ J ^ n)),
      (∀ r : R, rhoBar (Ideal.Quotient.mk (I ^ n) r) =
        Ideal.Quotient.mk (J ^ n) (algebraMap R C r)) ∧
      (∀ c : C, e (Ideal.Quotient.mk (J ^ n) c) =
        Ideal.Quotient.mk ((J ^ n).map (algebraMap C (C ⊗[R] B))) (c ⊗ₜ[R] (1 : B))) ∧
      (∀ (c : C) (b : B),
        e.symm (Ideal.Quotient.mk ((J ^ n).map (algebraMap C (C ⊗[R] B))) (c ⊗ₜ[R] b)) =
          Ideal.Quotient.mk (J ^ n) c * rhoBar (π b)) := by
  sorry

end Algebra.TensorProduct
