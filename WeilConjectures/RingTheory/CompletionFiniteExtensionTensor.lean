/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.CompletionFiniteExtensionTensorBijective

/-!
# Completed tensor product of a finite algebra

For a finite algebra `S` over a Noetherian ring `R` and a prime `p`, the tensor product
`R_p^∧ ⊗[R] S` is isomorphic to the `p`-adic completion of `R_p ⊗[R] S`.

## Implementation details

The isomorphism is `AdicCompletion.completionFiniteExtensionTensorMap`, which is bijective by
the completion-tensor equivalence for finite modules over a Noetherian ring.

## References

* [Stacks, Tag 07N9]
-/

@[expose] public section
universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- For a finite algebra `S` over a Noetherian ring `R` and a prime `p`, there is an
`S`-algebra equivalence between `R_p^∧ ⊗[R] S` and the `p`-adic completion of
`R_p ⊗[R] S`. -/
theorem completion_finite_extension_tensor
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    let _D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    Nonempty ((C ⊗[R] S) ≃ₐ[S] AdicCompletion J B) := by
  intro A m C B J Q D
  clear D Q
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
  exact ⟨AlgEquiv.ofBijective (completionFiniteExtensionTensorMap R S p)
    (completion_finite_extension_tensor_bijective R S p)⟩
end AdicCompletion
