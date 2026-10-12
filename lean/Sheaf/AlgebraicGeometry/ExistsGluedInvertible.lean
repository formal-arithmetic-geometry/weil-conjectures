/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullback

import Sheaf.AlgebraicGeometry.GlueComponentReducedCoverSections
import Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle

/-! # ExistsGluedInvertible

Source: Stacks Project, Varieties Lemma 09NE. -/

@[expose] public section
universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- Source: literature/stacks-project/varieties.tex, Varieties Lemma 09NE, proof.

Proof: Let T be the finite union of pairwise intersections. It is closed and discrete.
Off T the reduced closed cover is a disjoint open scheme cover. Around each t in T
choose a neighborhood meeting T only at t, exclude components not containing t, and
shrink to trivialize each component module. Cover the complement of T by trivializing
opens contained in individual components. Every overlap between different neighborhoods
lies off T. The reduced-cover section identity identifies the component frame changes
with units on these overlaps. Their cocycle identities hold componentwise, hence on Y.
Glue the rank-one trivial modules using these units. The local component frames give
isomorphisms of its pullbacks with the prescribed modules. These frames also prove
invertibility. With an empty index family the covering hypothesis forces Y empty and
its unique module is locally free of rank one vacuously.
(blueprint: lem-sc-exists-glued-invertible) -/
theorem existsGluedInvertible
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible] :
    ∃ N : Y.Modules, N.IsInvertible ∧
      ∀ a : ι, Nonempty ((tensorPullback (i a)).obj N ≅ M a) := by
  sorry
end AlgebraicGeometry.Scheme.Modules
