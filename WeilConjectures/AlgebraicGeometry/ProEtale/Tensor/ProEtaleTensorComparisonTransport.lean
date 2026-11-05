/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorTotalTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # Transport of representative-normalized tensor comparisons

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
(blueprint: lem-weil-pbc-proetale-tensor-comparison-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme
open ProjectionRestriction
attribute [local implicit_reducible] resolving proEtaleFlatRepresentatives
  proEtaleRingDerivedPullbackFactors proEtaleCanonicalTensorComparison
  CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf SheafOfModules.monoidalCategory
  proEtaleOrdinaryTensorPullback

end AlgebraicGeometry.Scheme
