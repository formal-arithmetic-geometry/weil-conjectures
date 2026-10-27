/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Sheaf.RingTheory.IsMittagLeffler
import Sheaf.RingTheory.FinitePresentationTensorProducts

/-!
# A universal tensor-kernel witness

Source: Stacks Project, Algebra, Tag 059M, proof of (2) implies (1), the first
commutative square; Tag 059K, implication (1) implies (2)
(blueprint: lem-trf-universal-tensor-kernel-witness).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open scoped TensorProduct

namespace Module

/-- A map from a finitely presented module to a tensor Mittag-Leffler module has a single
kernel element whose images give every kernel element for finitely presented test modules.
The witness module is a set-sized type. The test-module universe is arbitrary, independently
of the universes of the ring, source and target. No flatness is required.

Source: Stacks Project, Algebra, Tag 059M, proof of (2) implies (1), first square;
Tag 059K, implication (1) implies (2).
(blueprint: lem-trf-universal-tensor-kernel-witness)

Proof:
1. By def-sc-finitely-presented-module, present each finitely presented module as the
   cokernel of a finite matrix over R. These matrices form a set B of representatives.
   Put s = max u v w. Lift the representatives to Type s. Let A consist of pairs (Q, y)
   with Q in B and y in the kernel of f tensor id_Q. The quotient construction of
   def-weil-pbc-module-tensor-product makes each tensor a set, so A and T = product Q
   are sets in Type s, with componentwise module operations.
2. Apply lem-trf-finite-presentation-tensor-products to P and this family. Its bijective
   comparison sends some z in P tensor T to the family of the y. Thus each coordinate
   projection pi has (id_P tensor pi)(z) = y.
3. For a = (Q, y), naturality on pure tensors identifies the a-coordinate of the image
   of (f tensor id_T)(z) under the product comparison for M with (f tensor id_Q)(y) = 0.
   By def-trf-mittag-leffler-module this comparison is injective, so (f tensor id_T)(z) = 0.
4. Given a finitely presented test Q and x in its tensor kernel, choose a representative
   Q_a and a linear equivalence e : Q_a to Q. Pull x back along id_P tensor e.symm
   to obtain y. Tensor functoriality from def-weil-pbc-module-tensor-product shows y
   lies in the corresponding kernel. The pair (Q_a, y) is a coordinate of T.
   Set q = e composed with its projection. Then (id_P tensor q)(z) = x, using the
   coordinate equation and e composed with e.symm = id. This uses no flatness. -/
theorem exists_universal_tensor_kernel_witness
    (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (M : Type w) [AddCommGroup M] [Module R M]
    (hM : Module.IsMittagLeffler.{u, w, max u v w, max u v w} R M)
    (f : P →ₗ[R] M) :
    ∃ (T : Type (max u v w)) (_ : AddCommGroup T) (_ : Module R T),
      ∃ z : P ⊗[R] T, LinearMap.rTensor T f z = 0 ∧
        ∀ (Q : Type t) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q]
          (x : P ⊗[R] Q), LinearMap.rTensor Q f x = 0 →
          ∃ q : T →ₗ[R] Q, LinearMap.lTensor P q z = x := by
  sorry

end Module
