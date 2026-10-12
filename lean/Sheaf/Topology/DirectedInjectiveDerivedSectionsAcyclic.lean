/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Derived sections of directed colimits of injective sheaves

Source: Stacks Project, Cohomology, Lemma 01FF, final claim and its proof using 01EW.
(blueprint: lem-sc-directed-injective-derived-sections-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

/-- Directed colimits of injective abelian sheaves are acyclic for sections on compact opens.
Source: Stacks Project, Cohomology, Lemma 01FF, final claim, using Lemma 01EW.
(blueprint: lem-sc-directed-injective-derived-sections-acyclic).

Proof: let B be the compact opens and Cov the finite covers of members of B by members
of B. The basis hypothesis and compactness give finite compact refinements of all covers;
closure under binary intersections gives compactness of every nonempty finite intersection.
For every cover in Cov, sections on each intersection preserve directed colimits by the
degree-zero compact-open section theorem. Finite products preserve these colimits as well,
so the Cech complex of the colimit is the colimit of the Cech complexes of the injectives.
Injective sheaves have zero positive Cech cohomology. Exactness of filtered colimits of
abelian groups implies that the colimit complex also has zero positive cohomology.
Apply the Cech vanishing criterion to B and Cov to deduce vanishing of the right derived
sections on every member of B. This is simultaneously valid on all compact opens, as
required by the criterion. The empty open has zero sections; an empty covering gives
zero Cech complexes. No assertion that the colimit itself is injective is required. -/
theorem directedInjective_isZero_rightDerived_sections
    (X : Type u) [TopologicalSpace X]
    (hbas : ∀ (V : Set X), IsOpen V → ∀ x ∈ V, ∃ W : Set X, IsOpen W ∧
      IsCompact W ∧ x ∈ W ∧ W ⊆ V)
    (hint : ∀ (V W : Set X), IsOpen V → IsOpen W → IsCompact V → IsCompact W →
      IsCompact (V ∩ W))
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hJ : ∀ i : I, Injective (J.obj i))
    (U : Opens X) (hU : IsCompact (U : Set X)) (n : ℕ) :
    IsZero (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived
        (n + 1)).obj (colimit J)) := by
  sorry

end TopCat
