/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products of free rank-one modules

If `a` and `b` are free generators of the `R`-modules `A` and `B`, i.e. `r ↦ r • a` and
`r ↦ r • b` are bijective, then `a ⊗ₜ b` is a free generator of `A ⊗[R] B`.
-/

@[expose] public section

/-- **The tensor product of free generators is a free generator.** If `r ↦ r • a` and
`r ↦ r • b` are bijective, so is `r ↦ r • (a ⊗ₜ b)`. -/
lemma TensorProduct.bijective_smul_tmul {R A B : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] {a : A} {b : B}
    (ha : Function.Bijective fun r : R ↦ r • a) (hb : Function.Bijective fun r : R ↦ r • b) :
    Function.Bijective fun r : R ↦ r • (a ⊗ₜ[R] b) := by
  let eA := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R A a) ha
  let eB := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B b) hb
  have : (fun r : R ↦ r • (a ⊗ₜ[R] b)) =
      TensorProduct.congr eA eB ∘ (TensorProduct.lid R R).symm := by
    funext r
    simp [eA, eB, TensorProduct.tmul_smul]
  rw [this]
  exact (TensorProduct.congr eA eB).bijective.comp (TensorProduct.lid R R).symm.bijective
