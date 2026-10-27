/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentCompatibility

/-! # Object part of relative Proj twist descent

Source: Stacks Project, Constructions, Tag 01NR.
(blueprint: lem-trf-relative-proj-twist-chart-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

/-- The affine degree-one twists admit a descended module and local chart isomorphisms.

Source: Stacks Project, Constructions, Tag 01NR, object gluing portion of
`lemma-glue-relative-proj-twists`.

Proof: use the scalar-extension comparison on each affine restriction of the relative
Proj.  Its fraction formula gives identity and composition on refinements.  Refine
intersections of affine opens by affine opens and apply module-sheaf object descent to
the resulting cocycle.  The descended object and its local comparison isomorphisms are
the required `L` and `chart`; the same datum supplies the normalized scalar-extension
comparison and commuting chart square for every affine restriction. Empty opens are
covered by the zero module case.
(blueprint: lem-trf-relative-proj-twist-chart-descent-object).

The proof is the object-gluing component of the parent descent statement. -/
theorem exists_twist_chart_descent_object :
    ∃ (L : A.relProj.Modules),
      ∃ (chart : ∀ U : S.affineOpens,
        (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
          Proj.twist (A.grading U) 1),
      TwistChartCompatibility A L chart := by
  sorry

end AlgebraicGeometry.Scheme.GradedAlgebraData
