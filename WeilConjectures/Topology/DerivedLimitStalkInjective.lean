/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleDerivedSections
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.RingedSpaceSheafificationCohomology
import WeilConjectures.Topology.CohomologyPresheafDerivedSectionsEvaluation
import WeilConjectures.Topology.RingedSpaceRGammaDerivedLimit

/-!
# Stalk injectivity for a derived inverse limit

Source: Stacks Project, Cohomology of Sheaves, Tag 0D61,
lemma-cohomology-derived-limit-injective
(blueprint: lem-pc-ringed-space-derived-limit-stalk-injective).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

end AlgebraicGeometry.RingedSpace
