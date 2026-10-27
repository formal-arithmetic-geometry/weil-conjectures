/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] sfIntrinsicModuleEquivalence sfIntrinsicDerivedEquivalence
  ProEtale.projectionMapOfCompactification
attribute [local instance 100000] SheafOfModules.instAbelian
attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

/-! Endpoint comparison data for the ordinary projection. -/

/-- The two endpoint comparison isomorphisms used by the ordinary projection square.
Source: the endpoint comparison step of `lem-sf-ordinary-projection-reduction-arrow-comparison`.
(blueprint: lem-sf-ordinary-projection-endpoint-iso-data-q2). -/
structure IntegralOrdinaryProjectionEndpointData
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) where
  s : let A := Padic.coefficientExtensionRing l E (n + 1)
      letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
      (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L))).left ≅
      (Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))).left
  t : let A := Padic.coefficientExtensionRing l E (n + 1)
      letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
      (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L))).right ≅
      (Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))).right

/-- Endpoint comparison data exists for arbitrary completed inputs.
Source: the proper/open scalar comparison and constant-scalar realization in
`lem-sf-ordinary-projection-reduction-arrow-comparison`.
(blueprint: lem-sf-ordinary-projection-endpoint-iso-data-q2). -/
theorem integralOrdinaryProjection_endpointIsoData
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    Nonempty (IntegralOrdinaryProjectionEndpointData l E c aX aZ aY K L n) := by
  sorry

end WeilConjectures
