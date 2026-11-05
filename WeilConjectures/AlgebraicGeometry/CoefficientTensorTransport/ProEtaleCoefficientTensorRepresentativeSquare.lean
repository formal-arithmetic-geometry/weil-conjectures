/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
public import WeilConjectures.AlgebraicGeometry.CoefficientTensorChain.ProEtaleCoefficientTensorChainData
import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleTensorRepresentativeNormalization

/-! # Compatibility on flat K-flat representative pairs

(blueprint: lem-pbc-coefficient-restriction-tensor-representative-square)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

attribute [local implicit_reducible] pbcDerivedRestrict
  Functor.map₂HomologicalComplex Functor.mapHomologicalComplex
  SheafOfModules.restrictScalars

attribute [local irreducible] Functor.mapDerivedCategory
  proEtaleRingDerivedPullbackFactors CoefficientTensorChain.complexPullback
  pullback SheafOfModules.monoidalCategory proEtaleCanonicalTensorComparison
  proEtaleTensorPullbackTotalIso

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
