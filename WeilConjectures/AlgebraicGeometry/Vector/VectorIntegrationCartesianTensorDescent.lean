/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumCounit.VectorIntegrationDirectSumCounitMaps

import all Mathlib.Logic.Small.Defs

/-! # Cartesian transport of the tensor coefficient

Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, simultaneous trivializations and ordered affine counits.
(blueprint: def-pur-vector-integration-cartesian-tensor-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] rightDerivedLowerShriek upperStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme leftDerivedUpperStarComp
  leftDerivedUpperStarIsoMapDerivedCategory
attribute [local implicit_reducible] Scheme.Modules

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Cartesian transport of the tensor coefficient.
Source: blueprint vector-bundle purity proof, paragraph 2.
(blueprint: def-pur-vector-integration-cartesian-tensor-descent).

Proof: Compose the ordered coefficient descent, tensor pullback, the specified coefficient
comparison and the inverse tensor pullback. Every factor is a constructed isomorphism; no witness
is chosen.
-/
def vectorIntegrationCartesianTensorDescent
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X S T : Scheme.{u}} (p : X ⟶ S) (f : T ⟶ S)
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (L K : DerivedCategoryModule A S) (K' : DerivedCategoryModule A T)
    (cK : (ordinaryFinitePullback A f).obj K ≅ K')
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    (affineTraceRight A N hA T d).obj K' ≅
      (ordinaryFinitePullback A q).obj
        (((ordinaryFiniteTensor A X).obj
          ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj K)).obj
          ((ordinaryFinitePullback A p).obj L)) :=
  VectorIntegrationDirectSumCounit.coefficientDescent A N hA t T hT d K' ≪≫
    ordinaryFiniteTensorPullback A (affineTraceProjection T d)
      K' (affineLinearBaseCoefficient A N hA T d) ≪≫
    ordinaryFiniteTensorRightMapIso A (affineTraceTower T d)
      ((ordinaryFinitePullback A (affineTraceProjection T d)).mapIso cK.symm ≪≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).app K ≪≫
        (ordinaryFinitePullback A q).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).app K))
      ((ordinaryFinitePullback A (affineTraceProjection T d)).mapIso b.symm ≪≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).app L) ≪≫
    (ordinaryFiniteTensorPullback A q
      ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj K)
      ((ordinaryFinitePullback A p).obj L)).symm

end AlgebraicGeometry.Etale
