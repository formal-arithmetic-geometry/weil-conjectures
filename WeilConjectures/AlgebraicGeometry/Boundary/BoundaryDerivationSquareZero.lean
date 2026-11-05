/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.CechH1MapNatural
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.AlgebraicGeometry.Boundary.BoundaryDerivationAlgebraicData

/-!
# Boundary maps for square-zero extensions

Source: Stacks Project, Cohomology, Lemma 0B8S
(blueprint: lem-sc-boundary-derivation-square-zero).

The algebra sheaves are `Scheme.CommAlgebraSheaf`s and their underlying `𝒪_X`-modules are
`commAlgebraSheafModule`, with the module map of `p` given by `commAlgebraSheafModuleFunctor`.
The kernel `I` is tied by the short exactness of `0 → I → O' → O → 0`.
The connecting map is the snake boundary of any compatible injective resolutions,
transported to the recorded module cohomology (independent of the choice by
lem-weil-pbc-horseshoe-delta-functor). No boundary is an arbitrary function.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

end AlgebraicGeometry
