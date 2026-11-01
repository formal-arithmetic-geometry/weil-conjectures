/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
import WeilConjectures.SixFunctors.Integral.IntegralOrdinaryProjectionEndpointCompatibility

/-! # Finite scalar comparison of the ordinary projection arrow

Source: sk-thm-sf-pf-adic, reduction of the proper counit projection;
def-exchange-projection, proper/open composite.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
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

/- Finite reduction identifies the ordinary completed-coefficient projection arrow
with the realized fixed-scalar finite projection arrow. This is a compatibility of
specified maps, with no assertion that either projection is invertible and no
constructibility hypothesis.

Source: current blueprint sk-thm-sf-pf-adic, reduction paragraph, and
sk-thm-sf-pf-proetale, integral paragraph; Stacks Tags 07A4, 07A6, 099N.
(blueprint: lem-sf-ordinary-projection-reduction-arrow-comparison).

Proof: at the positive quotient, the coefficient projection is represented by the
cone of multiplication by the uniformizer power on the completed ring sheaf.
This two-term finite free resolution makes scalar extension commute with the
ordinary proper derived image. Scalar extension is a strong tensor functor;
its pullback comparison is fixed by the inverse-image coefficient square.
Together with the exact open scalar comparison these give invertible comparisons
between the endpoints of the reduced projection and the finite projection.
Transpose the proper square under the proper pull/direct adjunction. Both routes
are the scalar tensor comparison followed by the proper counit tensored with
identity: the scalar adjunction triangles give precisely this counit equation.
For the open square transpose the inverse open tensor comparison. Both routes
are the open unit followed by inverse tensor pullback. Full faithfulness of open
extension identifies these maps. The pullback compositor respects the coefficient
square, so pasting gives the compactification square. Finally the constant-scalar
realization equivalence identifies finite tensors on flat K-flat representatives,
proper adjunctions on K-injective representatives, and the exact open extension.
On each representative its tensor comparison sends a pure tensor to the same
sections; localization gives the specified tensor-model comparisons. Pasting
this realization square with the scalar square gives an isomorphism of arrows.
Only the perfect coefficient quotient is used for the proper scalar comparison;
the inputs can be unbounded and need not be complete. The argument includes the
residue quotient, empty schemes, identity opens and zero objects. -/
/-- Endpoint comparison data split from the finite reduction square.
Source: the proper/open scalar comparison and constant-scalar realization in
`lem-sf-ordinary-projection-reduction-arrow-comparison`. The source and target
comparisons are constructed from the proper and open mate squares, and their
compatibility is obtained by pasting those squares with the constant-scalar
realization.
(blueprint: lem-sf-ordinary-projection-endpoint-comparisons). -/
theorem integralOrdinaryProjection_endpointComparisons
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    ∃ (s : (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L))).left ≅
      (Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))).left)
      (t : (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L))).right ≅
      (Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))).right),
      s.hom ≫ ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L)))) =
        ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L)) ≫ t.hom
    := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  obtain ⟨e⟩ := integralOrdinaryProjection_endpointCompatibility l E c aX aZ aY K L n
  refine ⟨Arrow.leftFunc.mapIso e, Arrow.rightFunc.mapIso e, ?_⟩
  exact e.hom.w

theorem integralOrdinaryProjection_reduction_arrowComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    Nonempty (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L)) ≅
      Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))) := by
  obtain ⟨s, t, h⟩ := integralOrdinaryProjection_endpointComparisons l E c aX aZ aY K L n
  exact ⟨Arrow.isoMk s t h⟩

end WeilConjectures
