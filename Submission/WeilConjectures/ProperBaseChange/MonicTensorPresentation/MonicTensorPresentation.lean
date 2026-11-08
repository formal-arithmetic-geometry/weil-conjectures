/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- The finite free tensor algebra of the one-variable monic quotients. -/
abbrev Tensor (P : ι → R[X]) := ⨂[R] i, AdjoinRoot (P i)

end MonicTensorPresentation
