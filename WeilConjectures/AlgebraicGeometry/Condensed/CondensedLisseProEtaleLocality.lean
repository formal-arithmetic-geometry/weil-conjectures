/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

import WeilConjectures.CategoryTheory.ModuleObjects.ResidueOrdinary.IntegralResidueOrdinaryMonoidal
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.ProEtalePullbackInternalHom
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula

/-! # Pro-etale locality and pullback of dualizable condensed complexes

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3,
pullback paragraph before (3.1), Definition 3.3 and Lemma 4.5
(blueprint: lem-zl-condensed-lisse-proetale-locality).

The ordinary unbounded derived categories and their ordinary derived tensor are the
published internal-module constructions. Lisse means `Nonempty (HasRightDual K)`;
`HasRightDual` includes an exact evaluation/coevaluation pairing with both triangle identities.
No quasi-compactness or condition on irreducible components is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Mod.monoidalClosed
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] sheafBraidedCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] sheafSymmetricCategory sheafBraidedCategory
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory SymmetricCategory.ofCurried

end AlgebraicGeometry.ProEtale
