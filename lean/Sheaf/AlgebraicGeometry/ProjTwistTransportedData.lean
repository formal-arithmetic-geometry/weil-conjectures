/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import Sheaf.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# Standard generators of the transported polynomial Proj twist

Source: Stacks Project, Constructions, Lemma 01M7 (2),(3), and the chart and
transition steps of blueprint lem-sc-p1-proj-shifted-free-twist.
(blueprint: lem-sc-p1-proj-twist-transported-data)
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Transporting the polynomial Proj twist to the glued line gives the prescribed
local generators and transition relation; no comparison with another module is asserted.
Source: Stacks Project, Constructions, Lemma 01M7 (2),(3), and blueprint
lem-sc-p1-proj-shifted-free-twist, chart and overlap steps.
(blueprint: lem-sc-p1-proj-twist-transported-data)

Proof: write P = Proj k[x₀,x₁], Q = P¹_k, and M = O_P(d). On D₊(xᵢ), a section
of M is locally a homogeneous fraction of degree d. The element xᵢ is a unit in
the homogeneous localization. Its d-th power therefore makes sense for every integer d.
Multiplication by xᵢ^(-d) identifies the degree-d part with the degree-zero part,
with inverse multiplication by xᵢ^d. The fraction descriptions are compatible with
restriction, so these inverse maps identify M with the structure module on every
subopen of D₊(xᵢ), and xᵢ^d is its generator.
The equations C.chart_eq identify D₊(xᵢ) with the i-th standard chart of Q, and
identify x₁/x₀ with t. Pullback along C.iso.inv preserves these trivializations
and their free generators.
The induced structure-ring maps are isomorphisms on corresponding opens. On each of these
charts it sends the displayed free rank-one module to the free rank-one structure
module. Take gᵢ to be the image of xᵢ^d under this operation. For every subopen V
of the i-th chart the pulled-back trivializations give bijectivity of
a ↦ a • gᵢ|_V (Scheme.Modules.IsFreeGenerator.pullback_unit_app).
On the overlap, both x₀ and x₁ are units, and the identity
x₀^d = (x₀/x₁)^d x₁^d holds for all integer d. Transporting this equality along
the same ring and module maps gives g₀ = transitionUnit(d,0,1) • g₁.
These sections, the two bijectivity statements, and this equality are exactly the
five fields of TwistData. At d = 0 the generators are 1; at negative d the same
argument uses inverse powers of units, so no positivity hypothesis is needed. -/
theorem nonempty_twistData_pullback_inv (k : Type v) [Field k]
    (d : ℤ) (C : ProjectiveLine.ProjChartIsomorphism k) :
    Nonempty (ProjectiveLine.TwistData (Spec (.of k)) d
      ((Scheme.Modules.pullback C.iso.inv).obj
        (twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) d))) := by sorry

end AlgebraicGeometry.Proj
