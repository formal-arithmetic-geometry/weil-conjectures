/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.DirectImageLimitComparison

/-! # The scalar mate under the normalized direct-image realization

Source: the direct-image and final paragraphs of `lem-fix-operation-reduction`;
Stacks 06YY, 07A6, 0941
(blueprint: lem-weil-direct-image-scalar-realization-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
/-- The whole-system scalar mate and the ordinary completed-coefficient mate satisfy
this reconstruction square. This is equality of the specified maps, with no
invertibility assertion and no properness assumption.
Source: direct-image and final paragraphs of `lem-fix-operation-reduction`;
Stacks 06YY, 07A6, 0941
(blueprint: lem-weil-direct-image-scalar-realization-square).

Proof: compute on a flat-term K-flat representative of K and its actual quotient
system, retaining every quotient transition. Express reconstruction using the
reduction/total-limit unit and the normalized direct-image/limit comparison.
Express chi by its quotient maps and zero shifted Roos coordinate. Expand
coefficientExchange into scalarSourceComparison, realization of systemDirectScalar,
and the inverse scalar reduction counit. Naturality moves the direct-image counit
past these reduction maps. The scalar/pullback tensor reassociation carries a
section x tensor s tensor b to x tensor sb in either order. The ordinary and
system scalar mates therefore have the same geometric-adjunction transpose:
the geometric counit tensored with identity. The unit/counit triangle identities
cancel the inserted scalar-reduction comparison and its inverse. Both signed Roos
coordinates agree: the product coordinates are the quotient maps just computed,
and the shifted augmentation coordinate is zero. The normalized derived-unit
comparison transports this equality through K-injective direct-image and limit
models. Injectivity of the adjunction Hom equivalence proves the displayed
whole-system equality. Localization of the K-flat representatives gives it for K.
The argument includes identity coefficient maps, zero objects and empty schemes;
it neither assumes flatness of quotient-ring maps nor infers equality from finite
evaluations alone. -/
theorem directImageScalarRealizationSquare
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (CE : StrictDirectImageMixedUnit.LimitComparison l E f)
    (CL : StrictDirectImageMixedUnit.LimitComparison l L f)
    (K : sfIntegralConstructibleCategory l E X) :
    (completedDerivedScalarExtension l E L ι Y).map
        ((directImageReconstruction l E f CE).app K.obj) ≫
      (completedScalarComparison l E L ι Y).app
        ((FrobeniusExchange.integralDirectImage l E f).obj K.obj) ≫
      (FrobeniusExchange.coefficientExchange l E L ι
        (FrobeniusExchange.systemDirect l E f) (FrobeniusExchange.systemDirect l L f)
        (FrobeniusExchange.systemDirectScalar l E L ι f)).app K =
    (PurCompactSupport.properComparison (PurCompactSupport.completedChange l E L ι) f).app
        K.obj ≫
      (PurCompactSupport.push (PurCompactSupport.completed l L) f).map
        ((completedScalarComparison l E L ι X).app K.obj) ≫
      (directImageReconstruction l L f CL).app
        ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj) := by sorry

end WeilConjectures
