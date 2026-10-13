/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch

/-! # Source locality of one universal direct-image rank condition

Source: Stacks Project, Tag 0BDP, first three proof paragraphs, local rank conditions.
(blueprint: lem-sc-picard-single-rank-source-local).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Local single-rank conditions on a neighbourhood of every test point imply the condition.
No flatness, properness, connectedness or finite local freeness assumptions are needed.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs, local rank conditions.
(blueprint: lem-sc-picard-single-rank-source-local).

Proof:
1. Fix a further test h:T' to T and a point t'. Choose V around h(t') on which
   the condition holds. Its inverse image V' is an open neighbourhood of t'.
   Restrict h to a map V' to V, and apply the universal local condition on V at t'.
2. This supplies a still smaller open U in V', a rank r, and the direct-image and
   reference-module rank-r witnesses there. Regard U as an open subscheme of T'
   using the composite of open immersions.
3. Open base change identifies the restriction of p_*q^*F to V' with the direct
   image for the restricted test map. Tensor pullback composes up to its canonical
   isomorphism. These isomorphisms transport both rank witnesses to U as an open
   of T'. Hence the defining condition holds for h and t'. Empty test schemes
   have no points, so the conclusion is vacuous. -/
theorem picardUniversalSingleRankMatch_of_source_local {X S T : Scheme.{u}}
    (f : X ⟶ S) (E F : X.Modules) (g : T ⟶ S)
    (hlocal : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧
      PicardUniversalSingleRankMatch f E F (V.ι ≫ g)) :
    PicardUniversalSingleRankMatch f E F g := by sorry

end AlgebraicGeometry.Scheme
