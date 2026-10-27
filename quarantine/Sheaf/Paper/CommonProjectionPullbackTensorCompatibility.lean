/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.Paper.CommonProjectionTensorComparison
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # The common-stage tensor/pullback square

Source: thm-sf-pf-field.proof.md, Compatibility; the finite representative formula
of canonicalCommonStagePullbackTensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Transport a tensor/pullback comparison along the recorded functor equalities.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-pullback-tensor-compatibility). -/
def projectionTransportTensorComparison
    {A B : Type*} [Category* A] [Category* B]
    {F F' : A ⥤ B} {T T' : B ⥤ B ⥤ B} {U U' : A ⥤ A ⥤ A}
    (hF : F = F') (hT : T = T') (hU : U = U')
    (φ : (Functor.postcompose₂.obj F).obj U ≅
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T) :
    (Functor.postcompose₂.obj F').obj U' ≅
      (((Functor.whiskeringLeft₂ B).obj F').obj F').obj T' := by
  subst F'
  subst T'
  subst U'
  exact φ

/-- The supplied tensor/pullback comparison in the named operation coordinates.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-pullback-tensor-compatibility). -/
@[irreducible] def projectionPullbackTensor
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q) :
    (Functor.postcompose₂.obj (S.pull Q.p)).obj (T Q.Y) ≅
      (((Functor.whiskeringLeft₂ (B Q.Z)).obj (S.pull Q.p)).obj
        (S.pull Q.p)).obj (T Q.Z) :=
  projectionTransportTensorComparison A.properPull A.tensorBar A.tensorY A.stage.tensorPullback

/-- The curried version of an uncurried natural tensor comparison.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-pullback-tensor-compatibility). -/
@[irreducible] def projectionCurriedTensorComparison
    {A B : Type*} [Category* A] [Category* B]
    (V : A ⥤ B) (T : A ⥤ A ⥤ A) (T' : B ⥤ B ⥤ B)
    (t : Functor.uncurry.obj T ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj T') :
    (Functor.postcompose₂.obj V).obj T ≅
      (((Functor.whiskeringLeft₂ B).obj V).obj V).obj T' :=
  NatIso.ofComponents (fun a ↦ NatIso.ofComponents (fun b ↦ t.app (a, b)) (by
    intro b b' f
    simpa using t.hom.naturality (Prod.mkHom (𝟙 a) f))) (by
      intro a a' f
      ext b
      simpa using t.hom.naturality (Prod.mkHom f (𝟙 b)))

/-- The pullback/tensor square, with all its operation data supplied explicitly.
Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-pullback-tensor-compatibility). -/
@[irreducible] def projectionTensorComparisonCompatible
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category* (B X)]
    {B' : SixFunctorSpace D → Type*} [∀ X, Category* (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {V : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' V)
    (t : ∀ X, Functor.uncurry.obj (T X) ⋙ V X ≅
      (V X).prod (V X) ⋙ Functor.uncurry.obj (T' X))
    {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (A' : SixFunctorExchangeData S' T' Q) : Prop :=
  Adjunction.ComparisonCompatible (C.directAdjunction Q.p).left.symm
    (projectionPullbackTensor A).hom (projectionPullbackTensor A').hom
    (projectionCurriedTensorComparison (V Q.Z) (T Q.Z) (T' Q.Z) (t Q.Z))
    (projectionCurriedTensorComparison (V Q.Y) (T Q.Y) (T' Q.Y) (t Q.Y))

/-- Finite-stage inclusion preserves the canonical tensor/pullback comparison.
This is a square for pullback and tensor alone; no support functor, direct image,
projection mate, or adjunction counit occurs in the square.

Source: thm-sf-pf-field.proof.md, Compatibility, and the common finite coefficient
field paragraph; canonicalCommonStagePullbackTensor_existsUnique and its
pullbackTensorAtCommonStage representative formula.
(blueprint: lem-sf-common-projection-pullback-tensor-compatibility).

Proof: use the rational and common tensor and pullback normalization equalities
and the two tensorPullbackNormalization equations. The left comparison of the
coefficient adjunction is the identity on the prescribed finite-stage object
model by commonStageModelNormalization. For two inputs included from E, evaluate
the common-stage comparison at the common coefficient stage E. Its representative
is pullbackTensorAtCommonStage: the pullback transition, rational pullback of the
tensor transition, canonical rational tensor/pullback map, tensor of the two
inverse pullback transitions, and the inverse final tensor transition. Expand
the two inclusion tensorators using commonInclusionTensorModel and the scalar
unit for E to E. Naturality of the pullback and tensor transitions, and the
rational scalar compatibility of the tensor/pullback map, cancel the transition
maps on both sides and give the displayed square. Equality in the common-stage
Hom group follows by applying ofHom at E to this finite-stage equation. Transport
back by the normalization equalities. This argument applies to zero inputs,
empty schemes, and identity morphisms without additional assumptions. -/
theorem commonProjectionPullbackTensorCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D) :
    projectionTensorComparisonCompatible
      (S := (H.coefficientStages E).rational) (S' := H.commonStage)
      (T := (H.coefficientStages E).rationalTensor) (T' := H.commonStageTensor)
      (H.commonStageComparison E) (commonProjectionTensorComparison H E)
      ((H.coefficientStages E).rationalExchange Q) (H.commonStageExchange Q) := by sorry

end WeilConjectures
