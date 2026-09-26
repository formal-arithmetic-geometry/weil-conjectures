/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

/-!
# Finite continuous representations of a topological group

A representation of a topological group on a finite module is continuous for the discrete
topology on the module exactly when every stabilizer is open. This is the condition appearing
on the representation side of the Galois correspondence for finite local systems.

## Main definitions

- `Rep.IsFiniteContinuous`
-/

universe v w

namespace Rep

/-- Blueprint `sk-i-real-galois`: Galois correspondence for finite local systems.

A representation of a topological group `G` on a `Λ`-module is *finite continuous* if the
underlying module is finite and every stabilizer is open, i.e. the action is continuous for
the discrete topology on the module. For a profinite `G` this is exactly the condition
appearing in the Galois correspondence: a finite `Λ`-module with a continuous `G`-action.

This replaces `CategoryTheory.ContAction (ModuleCat Λ) G`, which cannot be formed because
`ModuleCat Λ` carries no `HasForget₂ _ TopCat` instance. -/
def IsFiniteContinuous {Λ : Type v} [CommRing Λ] {G : Type w} [Group G] [TopologicalSpace G] :
    CategoryTheory.ObjectProperty (Rep.{v} Λ G) :=
  fun X ↦ Finite X.V ∧ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x}

end Rep
