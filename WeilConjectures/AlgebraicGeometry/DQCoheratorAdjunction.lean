/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGeneration
import WeilConjectures.CategoryTheory.BrownRepresentabilityHomLocallySmall
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Coherator adjunction and detection by global sections

Source: Stacks Project, Tag 0B6I, final paragraph of the proof, and Derived Categories
of Schemes, `perfect-lemma-better-coherator`
(blueprint: lem-pc-dq-coherator-adjunction).

Derived global sections are expressed by their K-injective representatives: applying
`RingedSpace.globalSectionsFunctor` termwise to a K-injective complex represents RΓ.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

namespace DQComparisonAux

end DQComparisonAux

end AlgebraicGeometry
