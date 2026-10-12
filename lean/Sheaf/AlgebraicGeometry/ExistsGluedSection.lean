/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

import Sheaf.AlgebraicGeometry.GlueComponentReducedCoverSections
import Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle

/-! # ExistsGluedSection

Source: Stacks Project, Varieties Lemma 09NE. -/

@[expose] public section
universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- Source: literature/stacks-project/varieties.tex, Varieties Lemma 09NE, final assertion.

Proof: As in the construction of the glued module, choose neighborhoods of points of
T meeting T only at the chosen point. At such a point all sections on incident
components generate their line bundles by the nonvanishing hypothesis. Shrink the
neighborhood and normalize all frames to carry the prescribed sections to 1. Off T
use arbitrary trivializing frames. The reduced-cover section identity transfers the
frame changes on overlaps to units on Y. Glue the trivial modules with these transition
units. On the neighborhoods of T take the section 1; elsewhere take the expression of
the prescribed section in its component frame. These local expressions agree under the
transition maps because those maps are frame changes; the sheaf axiom produces t.
The component frame isomorphisms glue to the asserted pullback isomorphisms, under which
t restricts to s. The restriction is the unit of the tensor-pullback adjunction as in
the target statement. If T is empty the disjoint components simply glue independently.
(blueprint: lem-sc-exists-glued-section) -/
theorem existsGluedSection
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible]
    (s : ∀ a : ι, Γ(M a, ⊤))
    (hs : ∀ a b : ι, a ≠ b → Set.range (i a) ∩ Set.range (i b) ⊆
      i a '' nonvanishingLocus (M a) (s a)) :
    let res : ∀ (N : Y.Modules) (a : ι), Γ(N, ⊤) → Γ((tensorPullback (i a)).obj N, ⊤) :=
      fun N a t ↦ ((Classical.choose (exists_tensorPullbackAdjunction (i a))).unit.app N).val.app
        (op ⊤) t
    ∃ (N : Y.Modules) (t : Γ(N, ⊤)), N.IsInvertible ∧
      ∀ a : ι, ∃ e : (tensorPullback (i a)).obj N ≅ M a,
        e.hom.val.app (op ⊤) (res N a t) = s a := by
  sorry
end AlgebraicGeometry.Scheme.Modules
