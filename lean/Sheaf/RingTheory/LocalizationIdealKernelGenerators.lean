/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Localization of ideal multiplication kernels

Source: Stacks Project, Algebra, Tag 00MO, second proof paragraph;
Tags 00CS and 00DK for localization exactness and tensor compatibility.
(blueprint: lem-weil-pbc-localization-ideal-kernel-generators)
-/

@[expose] public section
universe u v w z t
open scoped TensorProduct
namespace Module

/-- Localization generates the new kernel from the ordinary base-change kernel.
Source: Stacks Project, Algebra, Tag 00MO, second proof paragraph, expanded using
Tags 00CS (localization exactness) and 00DK (tensor-localization compatibility).
(blueprint: lem-weil-pbc-localization-ideal-kernel-generators)

Proof: set A = S tensor_R R', N = R' tensor_R M and J = IR'. Tensor cancellation
identifies S' tensor_S M with the localization of N over A. Multiplication
J tensor_R' N -> N is A-linear, with A acting on N. Exactness of localization
identifies its localized kernel with the kernel of multiplication into S' tensor_S M.
Tensor-localization compatibility identifies the localized tensor product with
J tensor_R' (S' tensor_S M). Construct alpha as tensoring the canonical map
N -> S' tensor_S M, r' tensor x |-> rho'(r') times (1 tensor x), with J.
This formula is R'-balanced by the scalar tower identities and S-balanced by
the tensor relation, and hence defines an R'-linear map. Symmetry puts N first.
Every element of the localized kernel is a fraction of an element of the original
kernel. Such a fraction is the image under alpha multiplied by q(w)^{-1},
an S'-scalar, and therefore lies in the displayed S'-span. No quotient flatness,
Tor vanishing, finiteness or local hypotheses are used. If the localization set
contains zero, both the target module and its kernel are zero. -/
theorem exists_localization_ideal_kernel_generators
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (I : Ideal R) (M : Type t) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M]
    (hloc : ∃ (q : S ⊗[R] R' →+* S') (W : Submonoid (S ⊗[R] R')),
      (∀ (s : S) (r' : R'), q (s ⊗ₜ[R] r') =
        algebraMap S S' s * algebraMap R' S' r') ∧
      (letI := q.toAlgebra; IsLocalization W S')) :
    ∃ α : (R' ⊗[R] M) ⊗[R'] (I.map (algebraMap R R')) →ₗ[R']
        (S' ⊗[S] M) ⊗[R'] (I.map (algebraMap R R')),
      (∀ (r' : R') (x : M) (b : I.map (algebraMap R R')),
        α ((r' ⊗ₜ[R] x) ⊗ₜ[R'] b) =
          (algebraMap R' S' r' • ((1 : S') ⊗ₜ[S] x)) ⊗ₜ[R'] b) ∧
      (∀ z : (I.map (algebraMap R R')) ⊗[R'] (S' ⊗[S] M),
        TensorProduct.lift
          ((LinearMap.lsmul R' (S' ⊗[S] M)).comp
            (I.map (algebraMap R R')).subtype) z = 0 →
        TensorProduct.comm R' (I.map (algebraMap R R')) (S' ⊗[S] M) z ∈
          Submodule.span S'
            ((fun y : (I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M) ↦
              α (TensorProduct.comm R' (I.map (algebraMap R R')) (R' ⊗[R] M) y)) ''
              (LinearMap.ker (TensorProduct.lift
                ((LinearMap.lsmul R' (R' ⊗[R] M)).comp
                  (I.map (algebraMap R R')).subtype)) :
                Set ((I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M))))) := by
  sorry

end Module
