/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.RingTheory.IsMittagLeffler
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Mittag-Leffler quotient-product vanishing

Source: Stacks Project, Algebra, Tag 0AS6 (lemma-minimal-contains), the two displayed
quotient-product maps, and Tag 059M (proposition-ML-tensor), condition (2)
(blueprint: lem-trf-ml-quotient-product-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace Module

/-- For a Mittag-Leffler module `M`, the comparison from the tensor of a product of
quotients to the product of their tensors is injective. A tensor supported in every `N j`
vanishes after tensoring the quotient-product map.

Here `P = ∀ j : J, E ⧸ N j`, and `q = LinearMap.pi (fun j => (N j).mkQ)` sends `e` to
its family of quotient classes. The comparison `β` is the product of
`LinearMap.rTensor M (LinearMap.proj j)`; on `a ⊗ₜ m`, its `j`th coordinate is `a j ⊗ₜ m`.
The Mittag-Leffler test-module universe is `max u v t`, containing the quotients of `E`
after a canonical universe lift. No relation between the four universes is imposed.

Source: Stacks Project, Algebra, Tag 0AS6 (lemma-minimal-contains), the two displayed
quotient-product maps; Tag 059M (proposition-ML-tensor), condition (2)
(blueprint: lem-trf-ml-quotient-product-vanishing).

Proof:
1. The tensor symmetry `TensorProduct.comm` (lem-weil-pbc-module-tensor-comm) swaps pure
   tensors. Its inverse is the symmetry in the other order: both composites fix pure
   tensors, which generate (def-weil-pbc-module-tensor-product).
2. Apply def-trf-mittag-leffler-module to the family `E ⧸ N j` (lifting their universes
   when needed). It makes `M ⊗ P → ∏ j, M ⊗ (E ⧸ N j)` injective. Precompose with the
   symmetry on `P ⊗ M` and postcompose with the componentwise symmetries. This gives `β`,
   since both maps send `a ⊗ m` to `(a j ⊗ m)_j`, and pure tensors generate. Both symmetry
   maps are invertible, proving injectivity of `β`.
3. The `j`th coordinate of `β ((q ⊗ id)(x))` is `((N j).mkQ ⊗ id)(x)`, as follows on
   pure tensors and hence everywhere. Choose a lift of `x` in `N j ⊗ M` from the range
   hypothesis. The quotient map composed with the inclusion is zero, so tensor
   functoriality (def-weil-pbc-module-tensor-product) makes that coordinate zero.
   Every coordinate is zero; the injectivity from Step 2 gives `(q ⊗ id)(x) = 0`.
-/
theorem isMittagLeffler_quotient_product_vanishing
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {E : Type t} [AddCommGroup E] [Module R E] {J : Type w}
    (hML : Module.IsMittagLeffler.{u, v, w, t} R M) (N : J → Submodule R E) :
    Function.Injective
      (LinearMap.pi (fun j : J => LinearMap.rTensor M
        (LinearMap.proj j : (∀ k : J, E ⧸ N k) →ₗ[R] E ⧸ N j))) ∧
    ∀ x : TensorProduct R E M,
      (∀ j : J, x ∈ Set.range (LinearMap.rTensor M (N j).subtype)) →
      LinearMap.rTensor M (LinearMap.pi (fun j : J => (N j).mkQ)) x = 0 := by
  sorry

end Module
