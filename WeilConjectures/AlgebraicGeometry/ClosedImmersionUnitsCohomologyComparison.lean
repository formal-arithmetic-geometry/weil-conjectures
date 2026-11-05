/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ZariskiUnitsRestriction
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # The canonical closed-immersion comparison for units is bijective

Source: Stacks Project, Cohomology, Lemma 02UV, and Varieties, Lemma 09NY
(blueprint: lem-sc-closed-immersion-units-cohomology-comparison-bijective).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
