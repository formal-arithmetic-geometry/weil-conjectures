/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesBoundaryQuasiFinite

/-!
# Geometric compactification of the inverse image of a good-curves open

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, proof after
replacing the dense open by its inverse image under the finite good-curves cover.
(blueprint: lem-weil-pbc-good-curves-preimage-boundary)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open CategoryTheory.Limits

attribute [local instance high] instHasColimitOfHasColimitsOfShape
  hasColimitsOfShape_discrete

end AlgebraicGeometry.Etale
