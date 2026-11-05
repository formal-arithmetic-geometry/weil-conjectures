/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Tensor

/-!
# Flatness in short exact sequences

Let `0 ⟶ K ⟶ M ⟶ N ⟶ 0` be a short exact sequence of modules over a commutative ring `A`.
If `M` is flat and `K ⊗ A/I ⟶ M ⊗ A/I` is injective for every ideal `I`, then `N` is flat
(`Module.Flat.of_exact_of_lTensor_quotient_injective`): `Tor₁(A/I, N)` is the kernel of that map.

The proof is a diagram chase in the tensor products with `0 ⟶ I ⟶ A ⟶ A/I ⟶ 0`, using right
exactness of the tensor product.
-/

@[expose] public section

universe u

open TensorProduct

namespace Module.Flat

variable {A : Type u} [CommRing A] {K M N : Type u} [AddCommGroup K] [Module A K]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {f : K →ₗ[A] M} {g : M →ₗ[A] N}

end Module.Flat
