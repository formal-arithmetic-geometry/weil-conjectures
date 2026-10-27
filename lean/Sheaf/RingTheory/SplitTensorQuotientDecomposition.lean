/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Algebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Quotient decomposition of a split scalar-extended finite free algebra

Source: Stacks Project, Tag 0812 (lemma-trick-fitting-ideal), the quotient decomposition
following the algebra product splitting
(blueprint: lem-trf-split-tensor-quotient-decomposition).

The two tensor products carry the B-algebra structures through their second factors.
The applications of `id` supply these structures explicitly, without a local instance.
The two-term direct sum is represented by the module of pairs.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Quotienting a split scalar-extended finite free algebra gives the compatible decomposition
into its projected ideal quotients, and all four resulting modules are finite.
Source: Stacks Project, Tag 0812 (lemma-trick-fitting-ideal), quotient-decomposition passage
(blueprint: lem-trf-split-tensor-quotient-decomposition).

Proof plan:
1. Base-change the given basis using lem-weil-pbc-free-module-base-change-free, then flip
   tensor factors to obtain the B-basis `e i ⊗ 1`, including the empty basis.
2. By def-weil-pbc-module-tensor-product, pure tensors generate T. Tensor multiplication
   from lem-weil-pbc-algebra-tensor-pushout-universal-property gives
   `(c ⊗ b)(k ⊗ 1) = b • (ck ⊗ 1)`. Thus the B-span of these generators is an ideal,
   and it equals J since each ideal is closed under B-scalars.
3. Transport the generators through θ. Their first coordinates are f(k); multiplication
   by (1,0) and (0,1) separates the two coordinates. This proves θ(J) = KB × H.
4. The tensor pushout universal property constructs the map sending `[c] ⊗ b` to
   `[c ⊗ b]` in T/J. The quotient structures of def-weil-pbc-algebra-hom-quotient
   give its inverse by sending `[c ⊗ b]` to `[c] ⊗ b`. The composites fix pure tensors,
   which generate, so these are inverse B-algebra maps.
5. The product-ideal equality makes `[t] ↦ ([θ(t).1], [θ(t).2])` well-defined.
   Its inverse sends `([b],[d])` to `[θ.symm (b,d)]`. Composing with step 4 gives the
   asserted B-linear equivalence and its formula on pure tensors.
6. Project the finite basis expansions through θ to generate D; reduce these generators
   to generate D/H. The class of 1 generates B/KB. The images of `e i ⊗ 1` generate
   the quotient tensor product. These are finite generating families in the sense of
   def-weil-finitely-generated-module. Only finite sums for individual elements were used,
   so neither finite generation of K nor flatness of B over A is required. -/
theorem splitTensorQuotient_decomposition
    {A : Type u} {C : Type v} {B : Type w} {D : Type z}
    [CommRing A] [CommRing C] [CommRing B] [CommRing D]
    [Algebra A C] [Algebra A B] [Algebra B D]
    {d : ℕ} (e : Module.Basis (Fin d) A C) (f : C →ₐ[A] B) (K : Ideal C) :
    @_root_.id (∀ [Algebra B (C ⊗[A] B)] [Algebra B ((C ⧸ K) ⊗[A] B)], Prop)
      (fun [Algebra B (C ⊗[A] B)] [Algebra B ((C ⧸ K) ⊗[A] B)] ↦
        ∀ θ : C ⊗[A] B ≃ₐ[B] B × D,
          (∀ (c : C) (b : B), (θ (c ⊗ₜ[A] b)).1 = f c * b) →
          (∃ v : Module.Basis (Fin d) B (C ⊗[A] B),
            ∀ i : Fin d, v i = e i ⊗ₜ[A] (1 : B)) ∧
          (Ideal.map (includeLeftRingHom : C →+* C ⊗[A] B) K).restrictScalars B =
            Submodule.span B ((fun k : C ↦ k ⊗ₜ[A] (1 : B)) '' (K : Set C)) ∧
          Ideal.map θ.toRingHom (Ideal.map (includeLeftRingHom : C →+* C ⊗[A] B) K) =
            (Ideal.map f.toRingHom K).prod
              (Ideal.map ((RingHom.snd B D).comp
                (θ.toRingHom.comp (includeLeftRingHom : C →+* C ⊗[A] B))) K) ∧
          (∃ α : (C ⧸ K) ⊗[A] B ≃ₐ[B]
              (C ⊗[A] B) ⧸ Ideal.map (includeLeftRingHom : C →+* C ⊗[A] B) K,
            ∀ (c : C) (b : B), α (Ideal.Quotient.mk K c ⊗ₜ[A] b) =
              Ideal.Quotient.mk
                (Ideal.map (includeLeftRingHom : C →+* C ⊗[A] B) K) (c ⊗ₜ[A] b)) ∧
          (∃ γ : (C ⧸ K) ⊗[A] B ≃ₗ[B]
              (B ⧸ Ideal.map f.toRingHom K) ×
                (D ⧸ Ideal.map ((RingHom.snd B D).comp
                  (θ.toRingHom.comp (includeLeftRingHom : C →+* C ⊗[A] B))) K),
            ∀ (c : C) (b : B), γ (Ideal.Quotient.mk K c ⊗ₜ[A] b) =
              (Ideal.Quotient.mk (Ideal.map f.toRingHom K) (f c * b),
                Ideal.Quotient.mk (Ideal.map ((RingHom.snd B D).comp
                  (θ.toRingHom.comp (includeLeftRingHom : C →+* C ⊗[A] B))) K)
                  (θ (c ⊗ₜ[A] b)).2)) ∧
          Module.Finite B D ∧
          Module.Finite B (D ⧸ Ideal.map ((RingHom.snd B D).comp
            (θ.toRingHom.comp (includeLeftRingHom : C →+* C ⊗[A] B))) K) ∧
          Module.Finite B (B ⧸ Ideal.map f.toRingHom K) ∧
          Module.Finite B ((C ⧸ K) ⊗[A] B))
      (rightAlgebra (R := A) (A := C) (B := B))
      (rightAlgebra (R := A) (A := C ⧸ K) (B := B)) := by
  sorry

end Algebra.TensorProduct
