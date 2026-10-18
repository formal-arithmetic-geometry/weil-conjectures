/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Faithfully flat base change reflects universal injectivity

Source: Stacks Project, Algebra, Tag 05A5, `lemma-ffdescent-ML`, final reflection
argument, and Tag 05CK, `lemma-faithfully-flat-universally-injective`
(blueprint: lem-trf-faithfully-flat-universal-injective-reflection).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x t

namespace LinearMap

/-- A linear map is universally injective if and only if its scalar extension along a
faithfully flat ring map is universally injective. The map `f.baseChange S` is S-linear
with the action on the first tensor factor and sends `s ⊗ p` to `s ⊗ f p`.
The test universe is an arbitrary common upper bound for the rings and modules.

Source: Stacks Project, Algebra, Tag 05A5, `lemma-ffdescent-ML`, final reflection
argument; Tag 05CK, `lemma-faithfully-flat-universally-injective`
(blueprint: lem-trf-faithfully-flat-universal-injective-reflection).

Proof:
1. If f is universally injective over R, restrict any S-module T to R. Then
   `f.lTensor T` is injective. The canonical equivalence
   `TensorProduct.AlgebraTensorModule.cancelBaseChange` identifies it with
   `(f.baseChange S).lTensor T`, by the formula
   `t ⊗ (s ⊗ p) ↦ (s • t) ⊗ p`. This is
   `lem-trf-scalar-tensor-cancel-base-change`, using the tensor construction of
   `def-weil-pbc-module-tensor-product`.
2. Conversely, test universal injectivity over S on `S ⊗[R] L` for any R-module L.
   By `lem-trf-scalar-tensor-distrib-base-change`, the canonical equivalence
   `TensorProduct.AlgebraTensorModule.distribBaseChange`, sending
   `s ⊗ (l ⊗ p)` to `(s ⊗ l) ⊗ (1 ⊗ p)`, identifies this map with the
   scalar extension of `f.lTensor L`. Thus `S ⊗[R] (L ⊗[R] f)` is injective.
   Apply `lem-trf-faithfully-flat-ltensor-injective-reflection`, namely
   `Module.FaithfullyFlat.lTensor_injective_iff_injective`, to conclude that
   `f.lTensor L` is injective.
3. Since the tests are arbitrary, these implications give the equivalence. All tensor
   maps use `def-weil-pbc-module-tensor-product`, and the faithfully flat hypothesis is
   `def-weil-pbc-faithfully-flat-ring-map`, with no additional hypothesis on f.
-/
theorem universally_injective_iff_baseChange_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {P : Type w} {Q : Type x}
    [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q] (f : P →ₗ[R] Q) :
    (∀ (L : Type (max u v w x t)) [AddCommGroup L] [Module R L],
      Function.Injective (f.lTensor L)) ↔
    ∀ (T : Type (max u v w x t)) [AddCommGroup T] [Module S T],
      Function.Injective ((f.baseChange S).lTensor T) := by
  sorry

end LinearMap
