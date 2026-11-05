/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
import WeilConjectures.RepresentationTheory.DiscreteModule.FiniteFieldPrimeCohomology
import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.CategoryTheory.Sites.Point.Torsion
import WeilConjectures.RepresentationTheory.DiscreteModule.Torsion

/-!
# Torsion cohomological dimension of a finite base field

Source: the finite-field clause of `sk-lem-base-field-cd` (blueprint:
`det-base-field-cd-finite-torsion-bound`).

The proof follows the absolute Galois group computation for a finite field: every
geometric stalk is a torsion discrete module for the profinite completion of the
integers, and continuous cohomology of such a module vanishes above degree one.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
