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
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeRepresentative
import WeilConjectures.AlgebraicGeometry.CechHorseshoeLiftClass
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Injective middle term: the Čech local-lift cocycle is the connecting class

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EQ (proof via the double complex and
the maps `β` and `α⁻¹`) with Lemma 01EP, and the local-lift paragraph of Lemma 0B8S
(blueprint: lem-sc-boundary-cech-injective-middle).
-/

@[expose] public section

universe u wC wD

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
