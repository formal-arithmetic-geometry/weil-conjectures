/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.AlgebraicGeometry.BoundaryCechInjectiveMiddle
import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeRepresentative
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeGlobalLift
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeBoundaryIdentification
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.AlgebraicGeometry.CechHorseshoeLiftClass
import WeilConjectures.AlgebraicGeometry.CechHorseshoeCorrectionCochain
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The Čech local-lift representative computes the connecting boundary

Source: Stacks Project, Cohomology of Sheaves, Lemma 0B8S, local-lift description of the
boundary, with Lemma 01EQ for the Čech-to-cohomology map
(blueprint: lem-sc-boundary-cech-compatibility).
-/

@[expose] public section

universe u wC wD

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
