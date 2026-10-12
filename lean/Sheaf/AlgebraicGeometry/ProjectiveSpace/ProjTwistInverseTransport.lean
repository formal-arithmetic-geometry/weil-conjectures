/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Transport of a polynomial Proj twist to the projective line

Source: Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7;
Section 01MM, chart trivializations; blueprint lem-sc-p1-graded-resolution.
(blueprint: lem-sc-p1-proj-twist-inverse-transport).
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any chart-compatible comparison transports the Proj twist to the projective-space twist.
Source: Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7;
blueprint lem-sc-p1-graded-resolution, shifted-free clause.
(blueprint: lem-sc-p1-proj-twist-inverse-transport).

Proof: On D(x_i), the degree-d fractions form a rank-one module with generator x_i^d,
interpreted as a fraction when d is negative. On the overlap their relation is
x_0^d=t^(-d)*x_1^d. The chart equations of C identify these trivializations with the
standard projective-line charts, and their scalar actions with the chart rings.
Transporting along C inverse therefore gives the rank-one chart gluing with that
transition. The projective-space twist has the same trivializations and transition:
its definition is the base change of the integral Proj twist, and degree-d fractions
commute with this base change: on the integral chart the module is free on x_i^d,
so extension of scalars carries its generator to x_i^d over k; its overlap coefficient
(x_i/x_j)^d maps to the identical ratio over k. Map each transported generator to the corresponding
projective-space generator. The transition equation makes the local maps compatible,
so they glue. Glue their inverses as well; the composites fix the chart generators
and hence are identities. This covers every integer d, including zero. -/
theorem proj_twist_inverse_transport (k : Type u) [Field k]
    (C : ProjectiveLine.ProjChartIsomorphism k) (d : ℤ) :
    Nonempty ((Scheme.Modules.pullback C.iso.inv).obj
      (twist (homogeneousSubmodule (Fin 2) k) d) ≅
        ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) := by
  sorry

end AlgebraicGeometry.Proj
