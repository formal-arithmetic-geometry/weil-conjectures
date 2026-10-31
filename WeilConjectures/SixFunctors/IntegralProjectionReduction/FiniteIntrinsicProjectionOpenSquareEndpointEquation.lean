/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionOpenSquareEndpoint
public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionOpenCoordinates

/-! # Direct-image endpoint of the finite intrinsic projection square

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-open-square-endpoint-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection FiniteIntrinsicProjectionCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor finiteIntrinsicDerivedTensor
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence CompactSupportFiniteProjection.realization
  sixFunctorFiniteRealization integralCoefficientSheaf integralCoefficientCommRingSheaf
  compactSupportProjectionSquare fixedTensor tensor
  Over.homMk CostructuredArrow.homMk
  sixFunctorFiniteSupport sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  derivedTensorRightDerivedLowerStar


set_option maxHeartbeats 800000 in
-- Comparing the specified coefficient realizations needs additional elaboration heartbeats.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The direct-image inverse map and `beforeCompositor` reach the common endpoint.
Source: fix-prop-projection-formula.proof.md, same-map sentence; Stacks 0E8I and 07A4.
(blueprint: lem-sf-finite-intrinsic-projection-open-square-endpoint-equation).

Proof: expand beforeCompositor into the intrinsic tensor comparison, compact-support
realization and the pair of unary pullback coordinates. Write compact-support
realization as proper direct image of openComparison followed by the direct-image
comparison. Combine successive inverse realization maps in pullCoordinate by
functoriality. Naturality of the inverse coefficient unit moves the pullback of l
through this expression. The exact-to-left-derived comparison then identifies the
i-coordinate with inversePullback(i). Combining the inverse realization maps on the
g-coordinate gives the specified midpoint coordinate pp, formed from P_g(l), its exact
comparison, the exact-to-left-derived comparison and the coefficient unit. Move the resulting tensor
input map through direct-image comparison by naturality. Combine successive functor
maps and reassociate after precomposing the unchanged inverse open map. The word is
exactly the explicit endpoint. No midpoint or fixed-open projection equation occurs.
Only functoriality and natural isomorphisms are used, so zero inputs, empty and
identity opens, and m = 0 require no extra hypothesis. -/
theorem finiteIntrinsicProjectionOpenSquareEndpointEquation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    (proEtaleConstantDerivedDirectImage c.g
      (Padic.coefficientExtensionRing C.l E (m + 1))).map
        (SystemProjectionFormula.inverseOnDomain
          (SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
            X.obj.hom (c.g ≫ Y.obj.hom) m U
            ((finiteDerivedPullback C.l E m c.g).obj V))) ≫
      beforeCompositor m f c K L U V k l =
    finiteIntrinsicProjectionOpenSquareEndpoint m f c K L U V k l := by sorry

end WeilConjectures.IntegralProjectionReduction
