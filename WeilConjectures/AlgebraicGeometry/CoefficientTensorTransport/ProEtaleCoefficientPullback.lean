/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels

/-! # Normalization of exact derived coefficient pullback

(blueprint: lem-pbc-coefficient-pullback-factorization)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
attribute [local instance]
  AlgebraicGeometry.Scheme.proEtaleRingRestrictionPullbackInv_isIso
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.pbcDerivedRestrict
  Functor.mapHomologicalComplex SheafOfModules.restrictScalars
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  AlgebraicGeometry.Scheme.proEtaleRingDerivedPullbackFactors SheafOfModules.monoidalCategory

namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

end AlgebraicGeometry.Scheme.CoefficientTensorChain

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

end AlgebraicGeometry.Scheme.CoefficientTensorTransport

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

attribute [local irreducible] CoefficientTensorChain.complexPullback pullback

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
