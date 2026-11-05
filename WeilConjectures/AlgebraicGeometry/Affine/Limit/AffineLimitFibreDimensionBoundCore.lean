/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Fibre.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.Local.LocalFibreDimensionOpen

/-!
# Bad-locus contradiction for affine limit fibre dimensions

This is the bad-locus and Noetherian-fibre stabilization part of the affine limit dimension
argument. It is split from the final existence theorem so that the top-level implication remains
fully checked while this long construction can be proved independently.
Source: Stacks Project, Limits, Tag 05M5, `lemma-limit-dimension`.
(blueprint: lem-weil-pbc-affine-limit-fibre-dimension-bound-core).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
