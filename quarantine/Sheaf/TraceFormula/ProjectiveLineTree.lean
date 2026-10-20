/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.Data.Set.Card

/-! # Projective-line trees

Source: Temkin, *Stable modification of relative curves*, Appendix B, definition preceding
Corollary B.2 and its graph count, pp. 57–58 (blueprint: def-trf-projective-line-tree).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Closed nonsmooth points of the specified curve over its scalar field.
Smoothness is expressed by an actual smooth open neighbourhood.
Source: Temkin Appendix B, pp. 56–57 (blueprint: def-trf-projective-line-tree). -/
def curveNodes {k : Type u} [Field k] {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) : Set Z :=
  {z | IsClosed ({z} : Set Z) ∧ ¬ ∃ U : Z.Opens, z ∈ U ∧ Smooth (U.ι ≫ p)}

/-- A reduced connected nodal curve with projective-line components and a tree incidence
multigraph. In the finite connected incidence multigraph, the tree condition is exactly
`number of edges + 1 = number of vertices`. Edges are the actual nodes, so parallel edges
and self-nodes are counted separately; they cannot disappear by simplifying the graph.
A component is represented by its reduced closed embedding from the projective line,
compatibly with the scalar field. No reduction of `Z` is taken.
Source: Temkin Appendix B, definition preceding Corollary B.2 and its graph count,
pp. 57–58 (blueprint: def-trf-projective-line-tree). -/
def IsProjectiveLineTree {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) : Prop :=
  IsReduced Z ∧ ConnectedSpace Z ∧
  (∀ z ∈ curveNodes p, Orgogozo.IsOrdinaryDoublePoint p z) ∧
  (∀ W ∈ irreducibleComponents Z,
    ∃ j : ProjectiveLine (Spec (.of k)) ⟶ Z,
      IsClosedImmersion j ∧ Set.range j = W ∧
        j ≫ p = (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))) ∧
  (irreducibleComponents Z).Finite ∧ (curveNodes p).Finite ∧
  (curveNodes p).encard + 1 = (irreducibleComponents Z).encard

end AlgebraicGeometry
