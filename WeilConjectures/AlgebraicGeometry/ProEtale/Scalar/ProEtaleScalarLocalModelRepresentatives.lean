/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModelSurjectiveClosedReflection
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientSectionsLocalization
import all WeilConjectures.Algebra.Homology.SixFunctors.LocallyPrescribedModulesSmall
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.Order.CompletePartialOrder
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Small families of integral scalar local models

Source: blueprint main-20261015, `sk-lem-int-integral-heart-triangulated.proof.md`,
paragraph (2), final sentence
(blueprint: lem-sfb-proetale-scalar-local-model-representatives).

The site has objects in `Type (u + 1)` and morphisms in `Type u`; its module sections
and the representative index set live in `Type (u + 1)`. Scalar matrix quotients are
constructed before applying the existing constant-module scalar-extension functor.

## Main declarations

* `sfbScalarPresentationModule`: the actual quotient by a finite scalar matrix.
* `sfbIntegralScalarPresentationModel`: its existing scalar-extension realization.
* `proetale_scalar_local_model_representatives`: representatives and scalar matrix labels.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  CondensedRing.lowerStar
  Mod.extendScalarsIsoComapInv upperStarIsoLocalizationRestriction
  CondensedRing.upperStarLowerStarAdjunction

attribute [local irreducible] CondensedRing.upperStar

attribute [local instance] internalModules_grothendieck

end AlgebraicGeometry.ProEtale
