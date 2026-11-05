/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension

import all WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
import all WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import all WeilConjectures.AlgebraicGeometry.SixFunctors.EllCohomologicalDimensionComparison
import all WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.Integral.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.Integral.IntegralFiniteLevelDualClassical
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence

/-!
# The sections bound for the integral derived dual on classical torsion sheaves

Source: blueprint `sk-lem-int-ext.proof.md`, paragraph (2), finite-reduction bullets.
(blueprint: lem-route-integral-dual-torsion-heart-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option synthInstance.maxSize 4096

universe u v w x

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

namespace CondensedRing
end CondensedRing
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing
