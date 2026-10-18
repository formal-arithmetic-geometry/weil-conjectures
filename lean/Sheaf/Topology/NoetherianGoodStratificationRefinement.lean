/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible

/-!
# Finite good refinements of Noetherian locally closed partitions

Source: Stacks Project, Topology, Tag 09Y5,
`lemma-noetherian-partition-refined-by-stratification`, and Tag 09Y0,
`definition-good-stratification`
(blueprint: lem-sfb-noetherian-good-stratification-refinement).
-/

@[expose] public section

universe u v

namespace Topology

/-- A finite locally closed partition of a Noetherian space has a finite good refinement
with nonempty strata. The last clause explicitly expresses that every stratum closure is
a union of strata. When the space is empty, `n = 0` is allowed.

Source: Stacks Project, Topology, Tag 09Y5,
`lemma-noetherian-partition-refined-by-stratification`, and Tag 09Y0,
`definition-good-stratification`
(blueprint: lem-sfb-noetherian-good-stratification-refinement).

Proof:
1. Use the descending-chain condition to induct on closed subspaces, proving the assertion
   for every finite locally closed partition of each such subspace simultaneously. Closed
   subspaces inherit the condition. The empty subspace has the empty refinement.
2. In a nonempty subspace, rename it `T`. By
   `lem-sc-noetherian-finite-irreducible-components` and
   `lem-sc-irreducible-components-cover`, its distinct irreducible components form a finite
   nonempty closed cover. Their maximal irreducibility is
   `def-weil-irreducible-components`.
3. Choose a component `Z`, and let `O` be the complement of the other components. It is an
   open subset contained in `Z`, nonempty by irreducibility and maximality of components.
   The finitely many closed sets `closure (P a)` cover `T`, so irreducibility puts `Z` inside
   one of them. Write that `P a` as `V ∩ D`, with `V` open and `D` closed, using
   `def-weil-locally-closed-subset`. Then `Z ⊆ D`. The nonempty open `O` meets `P a`, since
   `O ⊆ Z ⊆ closure (P a)`. Thus `U = O ∩ V = O ∩ P a` is a nonempty open of `T` contained
   in this original part.
4. Put `C = T ∖ U` and `H = closure U ∖ U`. For every original part form
   `P a ∩ C ∩ closure U` and `P a ∩ C ∩ (closure U)ᶜ`, and discard empty pieces. They form a
   finite locally closed partition of the proper closed subspace `C`, refining the original
   partition and adapted to `H`: each piece lies in `H` or outside `closure U`.
5. Apply induction to this partition of `C`. Its refined parts are locally closed in `T`:
   an open of `C` is `C ∩ V` for an ambient open `V`, and a closed of the closed subspace
   `C` is ambient closed. Their ambient closures lie in `C` and agree with their subspace
   closures, so the good-stratification condition still holds for every pair of these parts.
6. Adjoin `U`. The old closures are contained in `C`, hence do not meet `U`. Each old part
   either lies in `H ⊆ closure U` or avoids `closure U`, so meeting `closure U` implies
   containment. The pair `(U, U)` satisfies containment automatically. These are all pairs;
   finiteness, nonemptiness, disjointness, local closedness and refinement are preserved.
   Every point of a stratum closure lies in a unique part of the partition; goodness puts
   that whole part inside the closure. Taking those parts gives the last union equality.
-/
theorem exists_finite_good_stratification_refinement
    {T : Type u} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    {A : Type v} [Finite A] (P : A → Set T)
    (hP_locallyClosed : ∀ a : A, IsLocallyClosed (P a))
    (hP_cover : (⋃ a : A, P a) = Set.univ)
    (hP_disjoint : Pairwise (fun a a' : A ↦ Disjoint (P a) (P a'))) :
    ∃ (n : ℕ) (Q : Fin n → Set T),
      (∀ b : Fin n, (Q b).Nonempty) ∧
      (∀ b : Fin n, IsLocallyClosed (Q b)) ∧
      (⋃ b : Fin n, Q b) = Set.univ ∧
      Pairwise (fun b c : Fin n ↦ Disjoint (Q b) (Q c)) ∧
      (∀ b : Fin n, ∃ a : A, Q b ⊆ P a) ∧
      (∀ b c : Fin n, (Q b ∩ closure (Q c)).Nonempty → Q b ⊆ closure (Q c)) ∧
      (∀ c : Fin n, ∃ I : Set (Fin n), closure (Q c) = ⋃ b ∈ I, Q b) := by
  sorry

end Topology
