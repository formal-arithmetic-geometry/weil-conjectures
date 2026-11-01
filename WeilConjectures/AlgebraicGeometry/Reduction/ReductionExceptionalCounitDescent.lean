/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects

/-! # Descent of the exceptional scalar counit equation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  reductionSiteScalarIso reductionSiteCompactSupportIso reductionDirectImageComparison
  reductionSite scalarExtensionFunctor

end AlgebraicGeometry.ProEtale
