/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentObject

/-! # Transition part of relative Proj twist descent

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

/-- A compatible descended chart family has additive transitions compatible with readings
and fractions.

Source: Stacks Project, Constructions, Tag 01NR, compatibility portion of
`lemma-glue-relative-proj-twists`.

Proof: use the supplied normalized scalar-extension comparison on a common affine
refinement.  Its
homogeneous fraction formula sends `a/f^k` to `res(a)/res(f)^k`, so the maps agree on
further refinements and satisfy the cocycle.  The induced maps on sections are additive;
the cocycle gives the equation with `twistChartRead`, and setting the denominator to one
gives the displayed equation for `twistChartFraction`.  The section-normalized tensor
adjunction identifies the ordinary restriction with the displayed reading map.
(blueprint: lem-trf-relative-proj-twist-chart-descent-transition).

The proof is the transition-compatibility component of the parent descent statement. -/
theorem exists_twist_chart_descent_transition
    (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
        Proj.twist (A.grading U) 1)
    (hcompat : TwistChartCompatibility A L chart) :
    ∀ (U V : S.affineOpens) (h : U ≤ V),
      ∃ t : Γ(Proj.twist (A.grading V) 1, A.twistChartOpen V) →+
          Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U),
        (∀ s : Γ(L, A.relProjHom ⁻¹ᵁ V.1),
          t (A.twistChartRead L chart V s) =
            A.twistChartRead L chart U
              (L.presheaf.map ((TopologicalSpace.Opens.map A.relProjHom.base).map
                (homOfLE (X := S.Opens) h)).op s)) ∧
        (∀ a : A.grading V 1,
          t (A.twistChartFraction V a) =
            A.twistChartFraction U ⟨A.res h a, (A.res h).map_mem a.property⟩) := by
  sorry

end AlgebraicGeometry.Scheme.GradedAlgebraData
