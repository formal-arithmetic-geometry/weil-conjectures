/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.CommonProjectionTensorComparison

/-! # Inclusion preserves the open tensor/pullback comparison

Source: thm-sf-pf-field.proof.md, Compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] ScalarLocalization.category

attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear
  rationalDerivedTensor commonStageTensorComparison operationStageTransitionIso
  sfRationalScalarExtension sfConstructibleIntegralScalarExtension
  sfIntegralScalarComp sfIntegralScalarUnit

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

/-- The inverse pullback/tensor square for an open factor, on arbitrary inputs.
It involves only the supplied pullback comparisons and the natural tensorator.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-open-pullback-tensor). -/
@[irreducible] def OpenPullbackTensorSquare
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {V : ∀ X, B X ⥤ B' X} {Q : SixFunctorCompactifiedSquare D}
    (c : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q) : Prop :=
  ∀ (M L : B Q.Z),
    (V Q.X).map ((A.openTensorPullback.inv.app M).app L) ≫
        (c.directAdjunction Q.i).left.hom.app (((T Q.Z).obj M).obj L) ≫
        (S'.pull Q.i).map ((t Q.Z).hom.app (M, L)) =
      (t Q.X).hom.app ((S.pull Q.i).obj M, (S.pull Q.i).obj L) ≫
        (Functor.uncurry.obj (T' Q.X)).map
          (Prod.mkHom ((c.directAdjunction Q.i).left.hom.app M)
            ((c.directAdjunction Q.i).left.hom.app L)) ≫
        (A'.openTensorPullback.inv.app ((V Q.Z).obj M)).app ((V Q.Z).obj L)

/-- Finite-stage inclusion preserves the inverse tensor/pullback comparison for
an open immersion. This is a square of tensor and pullback maps only: it uses
neither an open adjunction nor proper image or support identifications.

Source: thm-sf-pf-field.proof.md, Compatibility, the coefficient comparison for
pullback and tensor; canonicalCommonStagePullbackTensor_existsUnique, the formula
at every larger common finite field.
(blueprint: lem-sf-common-projection-open-pullback-tensor).

Proof: supply invertibility of the coefficient prime on Q.X and Q.Z using the
base-field structure maps. Transport the rational and common tensor functors and
pullbacks by their normalization equalities. The open tensor/pullback comparisons
are the canonical ones by rationalOpenTensorPullbackNormalization and
commonStageOpenTensorPullbackNormalization. Evaluate the representative equation
of canonicalCommonStagePullbackTensor_existsUnique at the field E on the included
pair M,L. The tensor comparisons at this stage, followed by the reflexive scalar
unit, are exactly commonInclusionTensorComparison; the pullback comparisons are
the prescribed model comparisons, whose components are identities by
commonStageModelNormalization. Substitute these descriptions in the representative
formula. The source and target transition isomorphisms cancel with their inverses,
leaving the forward tensor/pullback square. Conjugate that square by the two
canonical tensor/pullback isomorphisms to obtain the displayed inverse square.
All calculations take place at E, so no enlargement or arbitrary representative
is selected. The same identity-unit and isomorphism cancellation argument applies
to the empty scheme, zero inputs and identity pullbacks. -/
theorem commonProjectionOpenPullbackTensor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D) :
    OpenPullbackTensorSquare (H.commonStageComparison E) (commonProjectionTensorComparison H E)
      ((H.coefficientStages E).rationalExchange Q) (H.commonStageExchange Q) := by sorry

end WeilConjectures
