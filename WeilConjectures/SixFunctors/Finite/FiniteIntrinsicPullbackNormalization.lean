/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange

/-! # Unit normalization of finite intrinsic pullback

Source: Stacks 00YV and 07A6, uniqueness of adjoints and exact localization.
(blueprint: lem-sf-finite-intrinsic-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u
namespace WeilConjectures

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

end WeilConjectures
