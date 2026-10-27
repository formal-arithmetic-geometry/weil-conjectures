/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q63
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite lifts from a flat quotient-product tensor kernel

Source: Stacks Project, Tag 0AS6 (`lemma-minimal-contains`), proof, the kernel
identification after the second displayed map and the final finite-coefficient construction
(blueprint: lem-trf-flat-quotient-product-finite-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open scoped TensorProduct

namespace Module.Flat

/-- For a flat module, the tensor kernel of the map to a product of quotients is the
image of the tensor of the intersection inclusion; each kernel element already lifts
from a finitely generated submodule of the intersection. The quotient-product map is
`LinearMap.pi (fun j => (N j).mkQ)`, so its codomain is `∀ j, E ⧸ N j` with
componentwise operations. No surjectivity or Mittag-Leffler hypothesis is needed.

Source: Stacks Project, Tag 0AS6 (`lemma-minimal-contains`), proof, kernel calculation
and final paragraph (blueprint: lem-trf-flat-quotient-product-finite-lift).

Proof:
1. The quotient-product map kills `e` exactly when every quotient coordinate is zero,
   equivalently when `e` lies in every `N j`. Its kernel is therefore `⨅ j, N j`,
   including for an empty index type, when both submodules are the whole module.
2. Apply `Module.Flat.rTensor_exact` (lem-weil-pbc-flat-tensor-exact) to the exact
   pair consisting of the intersection inclusion and this quotient-product map.
   It gives the tensor kernel as the range of the tensored inclusion, without
   requiring surjectivity of the quotient-product map. Lift a kernel element `x`
   to a tensor in the intersection tensored with `M`.
3. Expand the lifted tensor as a finite sum of pure tensors, using generation by
   pure tensors from def-weil-pbc-module-tensor-product. Let `L` be the span in `E`
   of their finitely many first factors. Then `L.FG` and `L ≤ ⨅ j, N j`. Regard
   those first factors as elements of `L` and take the same finite tensor sum `z`.
   The formula for `LinearMap.rTensor` on pure tensors gives the required equality.
   For the zero tensor the empty sum gives `L = ⊥` and `z = 0`.
-/
theorem quotient_product_finite_lift
    {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M]
    {E : Type w} [AddCommGroup E] [Module R E]
    {J : Type t} (N : J → Submodule R E) :
    LinearMap.ker (LinearMap.pi (fun j : J => (N j).mkQ)) = (⨅ j : J, N j) ∧
      LinearMap.ker ((LinearMap.pi (fun j : J => (N j).mkQ)).rTensor M) =
        LinearMap.range ((⨅ j : J, N j).subtype.rTensor M) ∧
      ∀ x : E ⊗[R] M,
        (LinearMap.pi (fun j : J => (N j).mkQ)).rTensor M x = 0 →
          ∃ L : Submodule R E, L.FG ∧ L ≤ (⨅ j : J, N j) ∧
            ∃ z : L ⊗[R] M, L.subtype.rTensor M z = x := by
  sorry

end Module.Flat
