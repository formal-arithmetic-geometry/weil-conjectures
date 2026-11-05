/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# Uniform vanishing for torsion abelian higher direct images

Source: Stacks Project, Tag 0F10, and the separable-closure descent proof in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension`.
(blueprint: lem-kun-torsion-abelian-direct-image-dimension-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

end AlgebraicGeometry.Etale
