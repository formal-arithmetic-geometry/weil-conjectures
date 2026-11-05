/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! # Tensor presentations by monic equations

Source: Stacks Project, Morphisms, Tag 03HW, proof of lemma-massage-finite
(blueprint: lem-weil-pbc-monic-tensor-presentation).
-/

@[expose] public section

universe u v

open scoped TensorProduct
open Polynomial

namespace MonicTensorPresentation

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
variable {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable {S : Type u} [CommRing S] [Algebra R S]

@[simp] theorem tensorLift_tprod (g : ∀ i, A i →ₐ[R] S) (x : ∀ i, A i) :
    tensorLift g (PiTensorProduct.tprod R x) = ∏ i, g i (x i) := by
  simp [tensorLift]

@[simp] theorem tensorLift_single [DecidableEq ι] (g : ∀ i, A i →ₐ[R] S)
    (i : ι) (x : A i) :
    tensorLift g (PiTensorProduct.singleAlgHom i x) = g i x := by
  rw [PiTensorProduct.singleAlgHom_apply, tensorLift_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

@[simp] theorem presentationMap_root [DecidableEq ι]
    (P : ι → R[X]) (x : ι → S) (hx : ∀ i, aeval (x i) (P i) = 0) (i : ι) :
    presentationMap P x hx (PiTensorProduct.singleAlgHom i (AdjoinRoot.root (P i))) =
      x i := by
  unfold presentationMap
  rw [tensorLift_single, AdjoinRoot.liftAlgHom_root]

end MonicTensorPresentation
