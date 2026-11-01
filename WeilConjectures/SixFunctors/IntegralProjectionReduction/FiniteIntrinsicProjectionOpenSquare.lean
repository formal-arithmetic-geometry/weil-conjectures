/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionOpenCoordinates

/-! # Open comparison for the specified finite tensor realization

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-open-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection FiniteIntrinsicProjectionCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicDerivedEquivalence

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The coefficient coordinate square for the open tensor factor, before composing
inverse images. Neither the inverse-image compositor nor the constructible output
comparison occurs.

Source: Stacks 0E8I, 07A4; fix-prop-projection-formula.proof.md, same-map sentence.
(blueprint: lem-sf-finite-intrinsic-projection-open-square).

Proof: use the open extension/restriction adjunction to transpose the intrinsic
inverse open tensor map. Its transpose is the open unit tensored with identity,
followed by the inverse canonical tensor/pullback comparison. The coefficient
realization takes the open unit to the fixed open unit: this follows from the
ordinary conjugate adjunction and exact-adjunction localization. The representative
normalizations identify the scalar tensor/pullback square on flat-term K-flat pairs,
and naturality along resolving isomorphisms extends it to all derived inputs. Apply
this square to the transposes; the coefficient counits cancel by the triangle
identities. Injectivity of the adjunction identifies the inverse open maps. The
fixed map is an isomorphism, so its conjugate makes the intrinsic map invertible;
therefore inverseOnDomain is its inverse. Invert the square, move k and l through
its natural comparison isomorphisms, and apply proper direct image. Naturality of
sfIntrinsicDerivedDirectImageComparison and its composition with open realization
give exactly midpoint on the source and beforeCompositor on the target. This uses
no proper projection mate. The same unit and naturality equations cover zero inputs,
empty opens, identity opens and m=0. -/
theorem finiteIntrinsicProjectionOpenSquare
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    midpoint m f c K L U V k l ≫ fixedOpenPart m f c K L =
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).map
          (SystemProjectionFormula.inverseOnDomain
            (SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
              X.obj.hom (c.g ≫ Y.obj.hom) m U
              ((finiteDerivedPullback C.l E m c.g).obj V))) ≫
        beforeCompositor m f c K L U V k l := by sorry

end WeilConjectures.IntegralProjectionReduction
