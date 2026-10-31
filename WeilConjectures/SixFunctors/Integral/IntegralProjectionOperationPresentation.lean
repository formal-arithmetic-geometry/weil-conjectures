/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import all WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import WeilConjectures.SixFunctors.Integral.IntegralProperOperationProjection

/-! # Integral projection in ordinary completed-ring coordinates

Source: fix-prop-projection-formula.proof.md, integral reconstruction, and
def-exchange-projection, the proper-counit/open projection construction.
(blueprint: lem-sf-integral-projection-operation-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem arrowIsoOfIsoSource
    {B : Type v} [Category.{w} B] {P Q P' Q' : B}
    (p : P ⟶ Q) (q : P' ⟶ Q') (e : P ≅ P')
    (hp : IsIso p) (hq : IsIso q) : Nonempty (Arrow.mk p ≅ Arrow.mk q) := by
  let : IsIso p := hp
  let : IsIso q := hq
  refine ⟨Arrow.isoMk e ((asIso p).symm ≪≫ e ≪≫ asIso q) ?_⟩
  simp

private theorem stageProjection_isIso
    {DX DB DY DX' DB' DY' : Type v}
    [Category.{w} DX] [Category.{w} DB] [Category.{w} DY]
    [Category.{w} DX'] [Category.{w} DB'] [Category.{w} DY']
    (A : SuppliedExchangeProjection.ExchangeProjectionStage
      (DX := DX) (DB := DB) (DY := DY) (DX' := DX') (DB' := DB') (DY' := DY'))
    (K : DX) (L : DY)
    (hp : IsIso (((A.properAdjunction.rightAdjointProjectionMap
      A.tensorPullback.hom).app (A.openExtension.obj K)).app L)) :
    IsIso ((A.projection.app K).app L) := by
  let : IsIso (((A.properAdjunction.rightAdjointProjectionMap
      A.tensorPullback.hom).app (A.openExtension.obj K)).app L) := hp
  dsimp only [SuppliedExchangeProjection.ExchangeProjectionStage.projection,
    SuppliedExchangeProjection.compactificationProjectionFromData]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

private theorem dataProjection_isIso
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q)
    (K : B Q.X) (N : B Q.Y)
    (hp : IsIso ((A.stage.projection.app K).app N)) :
    IsIso (A.projectionComponent K N) := by
  let : IsIso ((A.stage.projection.app K).app N) := hp
  unfold SixFunctorExchangeData.projectionComponent
  infer_instance

private theorem operationProjection_isIso
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    IsIso (compactSupportProjectionComponent H.integralExchange f c K L) := by
  let Q := compactSupportProjectionSquare f c
  let A := H.integralExchange Q
  have hp : IsIso (((A.stage.properAdjunction.rightAdjointProjectionMap
      A.stage.tensorPullback.hom).app (A.stage.openExtension.obj K)).app L) :=
    integralProperOperationProjection_isIso H Q (A.stage.openExtension.obj K) L
  have hstage : IsIso ((A.stage.projection.app K).app L) :=
    stageProjection_isIso A.stage K L hp
  exact dataProjection_isIso A K L hstage

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  ProjectionRestriction.derived SemilinearSections.abelianSheafify
  SemilinearSections.locallyBijective SemilinearSections.sequenceSmall
  SemilinearSections.sliceSmall integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall
  constructibleTensorSiteSmall in
private theorem tensorPresentation
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)]
    (a : SfProEtaleProjection.TensorModel l E W)
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N) :
    Nonempty (a.tensor.obj (M, N) ≅ (integralCompletedTensor l E W).obj (M, N)) := by
  have presentation := constructibleTensorCompletion l E W
  let T := presentation.choose
  let e := presentation.choose_spec.choose
  let hchi := presentation.choose_spec.choose_spec.choose_spec
  let tau := hchi.2.2.choose
  have ht := hchi.2.2.choose_spec.2
  obtain ⟨P, ⟨p⟩⟩ := SfProEtaleProjection.goodRepresentative l E W M
  obtain ⟨Q, ⟨q⟩⟩ := SfProEtaleProjection.goodRepresentative l E W N
  have hP : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W)
      P.obj := P.property
  have hQ : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W)
      Q.obj := Q.property
  let z : a.tensor.obj (M, N) ≅ T.obj (M, N) :=
    a.tensor.mapIso (Iso.prod p q).symm ≪≫
      (a.representative.app (⟨P.obj, hP⟩, ⟨Q.obj, hQ⟩)).symm ≪≫
      e.app (P, Q) ≪≫ T.mapIso (Iso.prod p q)
  have htau : IsIso (tau.app (M, N)) := (ht M N hM hN).2
  exact ⟨z ≪≫ @asIso _ _ _ _ (tau.app (M, N)) htau⟩

/-- Changing the presentation of the integral operations identifies their projection
with the completed-unit extension of the ordinary proper/open projection. This is
a comparison within one coefficient category; it asserts no finite reduction or
invertibility of a projection.

Source: fix-prop-projection-formula.proof.md, adic reconstruction sentence;
def-exchange-projection, proper-counit/open composite; the presentation step of
lem-sf-integral-stage-projection-reduction.
(blueprint: lem-sf-integral-projection-operation-presentation).

Proof: expand the operation projection as the proper counit projection followed
by proper image of the supplied open projection isomorphism, conjugated by the
compact-support identification. Integral proper projection makes its proper
factor invertible, hence the whole operation projection is invertible. Independently,
the concrete pro-etale projection theorem makes integralMap invertible. Compare
the source objects: the support value equality and qcqs support realization identify
the support input; the tensor normalization of H and the two signed-total tensor
presentations identify its tensor with the completed ordinary tensor. Tensor
completion on constructible pairs and the source completion unit are isomorphisms.
If e is this source isomorphism and p,q are the two invertible arrows, their target
isomorphism is p inverse followed by e followed by q. Cancellation proves the square,
and Arrow.isoMk gives the claimed isomorphism. The statement specifies no endpoint
components of that isomorphism, so this argument needs no separate canonical-map
normalization equation. No separated structure morphism or extra Tor hypothesis
is used. Zero inputs, empty schemes and identity-open compactifications are covered
by the same construction. -/
theorem integralProjection_operationPresentation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (aX : SfProEtaleProjection.TensorModel C.l E X.obj.left)
    (aZ : SfProEtaleProjection.TensorModel C.l E c.Z)
    (aY : SfProEtaleProjection.TensorModel C.l E Y.obj.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    Nonempty (Arrow.mk (compactSupportProjectionComponent H.integralExchange f c K L).hom ≅
      Arrow.mk (SfProEtaleProjection.integralMap C.l E D C.different f.hom.left c
        aX aZ aY K L).hom) := by
  let hl := PurCompactSupport.coefficientPrimeUnit C.l D C.different
  let : IsLocallyNoetherian Y.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y.obj.left ↘ Spec (.of D.k))
  let : CompactSpace Y.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace (Y.obj.left ↘ Spec (.of D.k))
  let : IsNoetherian Y.obj.left := ⟨⟩
  let (y : Y.obj.left) : Invertible (C.l : Y.obj.left.residueField y) :=
    (SfProEtaleProjection.residue_unit C.l D C.different Y.obj.left y).invertible
  let PK := (H.integral.support f c).obj K
  let s : PK.obj ≅ (PurCompactSupport.image (PurCompactSupport.completed C.l E) c).obj
      K.obj :=
    eqToIso (congrArg (fun V ↦ V.obj)
      ((H.supportConstruction f hl c).choose_spec.2.2.1 K)) ≪≫
      eqToIso (congrArg (fun V ↦ V.obj)
        (sfCompactSupportFiniteIntegralFunctor_obj C.l D.k hl c E K).symm) ≪≫
      ((sfQcqsCompactSupportRealization C.l E D.k hl c).app K).symm
  have hPK := (sfIntegralConstructible C.l E Y.obj.left).prop_of_iso s PK.property
  obtain ⟨t⟩ := tensorPresentation C.l E Y.obj.left aY _ L.obj hPK L.property
  let d := IntegralOnSlice.completionUnit C.l E Y.obj.left none
  have hd : IsIso (d.app
      (SfProEtaleProjection.ordinarySource C.l E c aY K.obj L.obj)) :=
    (SfProEtaleProjection.integralDomains C.l E D C.different f.hom.left c
      aX aY K L).1
  let e : (((H.integralTensor Y).obj PK).obj L).obj ≅
      SfProEtaleProjection.completedSource C.l E c aY K.obj L.obj :=
    eqToIso (congrArg (fun T ↦ (((T.obj PK).obj L).obj))
      (H.integralTensorNormalization Y)) ≪≫
      (integralCompletedTensor C.l E Y.obj.left).mapIso (Iso.prod s (Iso.refl L.obj)) ≪≫
      t.symm ≪≫ @asIso _ _ _ _
        (d.app (SfProEtaleProjection.ordinarySource C.l E c aY K.obj L.obj)) hd
  have hp := operationProjection_isIso H f c K L
  have hq := SfProEtaleProjection.integral_isIso C.l E D C.different f.hom.left c
    aX aZ aY K L
  exact arrowIsoOfIsoSource
    (compactSupportProjectionComponent H.integralExchange f c K L).hom
    (SfProEtaleProjection.integralMap C.l E D C.different f.hom.left c
      aX aZ aY K L).hom e
    (((sfIntegralConstructible C.l E Y.obj.left).ι.mapIso
      (@asIso _ _ _ _ (compactSupportProjectionComponent H.integralExchange f c K L)
        hp)).isIso_hom)
    (((sfIntegralConstructible C.l E Y.obj.left).ι.mapIso
      (@asIso _ _ _ _ (SfProEtaleProjection.integralMap C.l E D C.different
        f.hom.left c aX aZ aY K L) hq)).isIso_hom)

end WeilConjectures
