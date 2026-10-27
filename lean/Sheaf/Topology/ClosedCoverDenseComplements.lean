/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.Topology.Irreducible

/-!
# Distinct components from a finite closed cover with dense relative complements

Source: Stacks Project, More on Morphisms, Tag 0554,
`lemma-irreducible-components-in-neighbourhood`, final paragraph, retaining the
nowhere-dense intersection hypothesis established earlier in that proof
(blueprint: lem-trf-closed-cover-dense-complements-component-injection).
-/

@[expose] public section

universe u v

set_option autoImplicit false

namespace Topology

/-- A finite closed cover with nonempty pieces and dense pairwise relative complements
admits private points and an injective family of irreducible components containing them.
Density is taken in the subspace `E i`; the components are components of the ambient space.

Source: Stacks Project, More on Morphisms, Tag 0554, final paragraph, with its earlier
nowhere-dense intersection hypothesis; Topology, Tags 004V, 004W (4), and 0G2Y.
(blueprint: lem-trf-closed-cover-dense-complements-component-injection)

Proof plan:
1. If `I` is empty, the cover forces the ambient space to be empty; use empty families.
2. For fixed `i`, the finitely many complements of `E j`, for `j ≠ i`, are dense open
   subsets of `E i`. Inductively intersecting them with the nonempty open `E i` leaves a
   nonempty open subset: a dense set meets every nonempty open. Choose `x i` there.
3. By `lem-sc-irreducible-components-cover`, namely `mem_irreducibleComponent` and
   `irreducibleComponent_mem_irreducibleComponents`, choose a component `K i` containing
   `x i`; this needs no separation or Noetherian hypothesis.
4. By `def-weil-irreducible-components`, `K i` is nonempty and irreducible. Intersecting
   the finite closed cover with `K i` and inducting on its size shows that `K i` lies
   in some `E j`: the empty cover is impossible, and the induction step separates one
   closed member from the finite union of the others and applies irreducibility.
   The private-point property forces `j = i`, so `K i ⊆ E i`.
5. If two selected components coincide, the private point of the first lies in the
   covering piece of the second, a contradiction unless their indices coincide.
   Thus the family of components is injective, equivalently pairwise distinct. -/
theorem exists_injective_components_of_closed_cover_dense_complements
    {T : Type u} [TopologicalSpace T] {I : Type v} [Finite I]
    (E : I → Set T) (h_nonempty : ∀ i : I, (E i).Nonempty)
    (h_closed : ∀ i : I, IsClosed (E i))
    (h_cover : (⋃ i : I, E i) = Set.univ)
    (h_dense : ∀ i j : I, i ≠ j → Dense {x : E i | (x : T) ∉ E j}) :
    ∃ (x : I → T) (K : I → irreducibleComponents T),
      (∀ i : I, x i ∈ (K i : Set T) ∧ (K i : Set T) ⊆ E i ∧
        ∀ j : I, j ≠ i → x i ∉ E j) ∧ Function.Injective K := by
  sorry

end Topology
