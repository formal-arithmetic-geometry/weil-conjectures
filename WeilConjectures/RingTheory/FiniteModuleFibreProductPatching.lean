/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.FlatModuleFibreProductPatching
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite modules over a surjective ring fibre product

Source: Stacks Project, More on Algebra, Tag 0D2H,
`lemma-finite-module-over-fibre-product`, in Situation 08KH
(blueprint: lem-sfb-finite-module-fibre-product-patching).

We reuse the canonical compatible-module pullback from the flat-patching module.
Its construction does not require flatness. Extension along the surjection q is
canonically M'/ker(q)M'; tensor symmetry gives the node's N tensor_B A convention.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.FibreProductPatching

/-- Compatible finite modules patch to a finite module over the ring fibre product.
Source: Stacks Project, More on Algebra, Tag 0D2H,
`lemma-finite-module-over-fibre-product`, in Situation 08KH
(blueprint: lem-sfb-finite-module-fibre-product-patching).

Proof:
1. The ring projection R → B is onto by surjectivity of q. The module projection
   P → N is onto because M' → M'/IM' is onto. Choose finite generators y_i of N
   and x_i of M' using [def-weil-finitely-generated-module], and lifts u_i of y_i.
2. By [lem-sfb-patched-module-base-change], P tensor_R A' is canonically M'.
   Express the inverse images of the x_i as finite sums of pure tensors using
   [def-weil-pbc-module-tensor-product]. Collect their first factors v_j in P.
   Their second-coordinate images generate M' over A'. This does not assert
   that the projection P → M' is onto.
3. For ξ in P, express its first coordinate using the y_i and lift the B-coefficients
   to R. Subtract the resulting combination of u_i. The remainder is (0, θ),
   where θ belongs to IM'. Expand θ as a finite sum of ideal multiples, then
   expand those module elements using the second coordinates of the v_j.
   Regroup to obtain θ = ∑ t_j ρ(v_j) with each t_j in I.
4. Each s_j = (0, t_j) lies in R and satisfies s_j v_j = (0, t_j ρ(v_j)).
   Thus ξ is a combination of the u_i and v_j. These finite lists generate P,
   as required by [def-weil-finitely-generated-module]. Empty lists and zero
   rings are included; no finiteness condition on I was used.
-/
theorem finite_patchedModule
    {A A' B : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (hq : Function.Surjective q)
    (N : ModuleCat.{max u v} B) (M' : ModuleCat.{max u v} A')
    (φ : (extendScalars b.hom).obj N ≅ (extendScalars q.hom).obj M')
    [Module.Finite B N] [Module.Finite A' M'] :
    Module.Finite (pullback (C := CommRingCat) b q) (patchedModule b q N M' φ) := by
  sorry

end ModuleCat.FibreProductPatching
