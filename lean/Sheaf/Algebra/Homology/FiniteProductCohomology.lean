/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Cohomology of finite products of cochain complexes

Source: `literature/stacks-project/homology.tex`, elementary homology of finite products
of complexes, formulation supplied by the stage-1 worker
(blueprint: lem-weil-pbc-finite-product-complex-cohomology).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

/-- The canonical comparison from the cohomology of a finite product of cochain complexes
of abelian groups to the product of their cohomologies is an isomorphism in every degree.
The product of complexes is computed degreewise. The comparison is induced by the coordinate
projections, hence is natural in the family of complexes; `piComparison_comp_π` identifies
its coordinates with the cohomology maps of those projections.

Source: `literature/stacks-project/homology.tex`, elementary homology of finite products
of complexes, formulation supplied by the stage-1 worker.

Proof: The product differential is coordinatewise, so its cycles are tuples of cycles.
Its boundaries are tuples of boundaries: choose a preimage for each coordinate to obtain
one preimage in the product. The coordinate quotient maps therefore induce a homomorphism
from the quotient of cycles by boundaries to the product of the coordinate quotients.
Its kernel is zero, since a tuple maps to zero precisely when each coordinate is a boundary.
It is surjective, since representatives of the coordinate classes assemble into a tuple
of cycles. This is the comparison induced by the projections. All these maps commute with
morphisms of complexes, which gives naturality, for each integer degree.
(blueprint: lem-weil-pbc-finite-product-complex-cohomology) -/
theorem homology_finite_product_comparison_isIso
    (I : Type w) [Finite I] (K : I → CochainComplex AddCommGrpCat.{u} ℤ) (q : ℤ) :
    IsIso (piComparison (homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q) K) := by
  sorry

end HomologicalComplex
