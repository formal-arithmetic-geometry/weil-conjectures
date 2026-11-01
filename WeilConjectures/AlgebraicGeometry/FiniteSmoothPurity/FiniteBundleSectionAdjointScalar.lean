/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteVectorIntegrationScalar
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSectionCompositor
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate

/-! # Coefficient compatibility of the bundle zero-section integration adjunct

Source: blueprint/latest, smooth-purity reduction compatibility proof (3), Orientation,
and vector-bundle-purity proof, paragraph 2.
(blueprint: lem-sp-finite-bundle-section-adjoint-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12
  cachedEtaleTensor23 cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

end AlgebraicGeometry.Etale.FiniteSmoothPurity
