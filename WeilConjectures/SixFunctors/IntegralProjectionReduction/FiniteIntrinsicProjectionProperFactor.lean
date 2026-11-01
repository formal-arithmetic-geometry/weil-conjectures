/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionCoordinates
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProperCoordinates
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProperEndpoint

/-! # Proper comparison for the specified finite tensor realization

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-proper-factor).
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
  pullbackTensorCalculus sfIntrinsicModuleEquivalence
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor finiteIntrinsicDerivedTensor
  rightDerivedLowerStarProjectionMap SystemProjectionFormula.finiteProperProjection
  FiniteIntrinsicRealization.openCoordinate FiniteIntrinsicRealization.inversePullback
  FiniteIntrinsicRealization.inverseDirectImage
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  CompactSupportFiniteProjection.realization sixFunctorFiniteRealization
  integralCoefficientSheaf integralCoefficientCommRingSheaf

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The proper counit mate commutes with the specified tensor realization. Only the
proper factor occurs; the open projection and the pullback compositor do not occur.

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 07A4.
(blueprint: lem-sf-finite-intrinsic-projection-proper-factor).

Proof: apply the inverse coefficient equivalence at the output, and then the Hom
bijection of the fixed inverse-image/direct-image adjunction. The intrinsic proper
factor transposes to the finite tensor/pullback comparison followed by the actual
counit tensored with identity. The finite scalar tensor realization is induced by the
ordinary balanced tensor comparison on simultaneous flat K-flat representatives.
On those representatives its square with inverse image sends a pure tensor to the same
two pulled-back sections. Descend that square through the two localization functors.
The section-normalized inverse-image comparison identifies the actual units, hence
the counits, of the intrinsic and fixed adjunctions. Substitute this counit equation
in the transposed square; tensor naturality moves k and l to the endpoints.
The direct-image realization comparison is normalized on K-injective representatives,
so the resulting target comparison is exactly midpoint. Expand sourceComparison and
supportRealization: inverse finiteSupport cancels finiteSupport, and the open
coefficient unit cancels with the open realization in midpoint. The coefficient
triangle identities cancel the remaining inner units. Adjunction injectivity and
faithfulness of the coefficient equivalence give the equation. No invertibility of
the proper projection is used. Zero inputs, empty schemes and m=0 satisfy the same
unit and representative equations. -/
theorem finiteIntrinsicProjectionProperFactor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    (SystemProjectionFormula.finiteProperProjection C.l E D C.different c.g
      (c.g ≫ Y.obj.hom) Y.obj.hom m
      (((sfIntrinsicExtensionByZero c.i
        (Padic.coefficientExtensionRing C.l E (m + 1))).mapDerivedCategory).obj U) V) ≫
        midpoint m f c K L U V k l =
      ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Y).hom.app
        ((sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).obj U, V) ≫
        (evaluatedTensor (C := C) (E := E) m Y).map
          (Prod.mkHom ((sixFunctorFiniteSupport D C E (m + 1)
            (Nat.le_add_left 1 m) f c).map k.hom ≫
              (S.finiteSupport f c).inv.app K) l.hom)) ≫
        (sourceComparison S f c K L).hom ≫ fixedProper m f c K L := by
  have hp := intrinsic_proper_coordinates (C := C) (E := E) m f c K L U V k l
  have he := intrinsic_proper_endpoint_coordinates (C := C) (E := E) m S f c K L U V k l
  exact hp.trans (he _ (fixedProper m f c K L))

end WeilConjectures.IntegralProjectionReduction
