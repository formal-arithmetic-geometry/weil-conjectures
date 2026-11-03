/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.FactorEvaluation.IntegralProjectionFactorEvaluationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenFiniteEvaluation

/-! # Evaluation of the unary open coefficient comparison

Source: prop-sf-pf-coherence, compatibility with extension by zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor scalarReductionDerivedExtension
  scalarReductionDerivedRestriction

attribute [local implicit_reducible] identitySquare sixFunctorFiniteOpen
  sixFunctorIntegralReduction coefficientFiniteDerivedExtension
  Over.homMk CostructuredArrow.homMk scalarReductionSourceDerived
  scalarReductionTargetDerived integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralOperationsCommHasDerivedCategory integralCompletedRingHasDerivedCategory
  integralTowerHasDerivedCategory coefficientFiniteHasDerived reductionModulesHasDerivedCategory
  SemilinearSections.moduleAbelian

private theorem and_rec_eq {P Q : Prop} {α : Sort*} (h : P ∧ Q) (g : P → Q → α) :
    And.rec g h = g h.1 h.2 := by
  cases h
  rfl

private theorem identity_i_left {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).i.hom.left = c.i := rfl

private theorem identity_Z_left {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).Z.obj.left = c.Z := rfl

private theorem identity_X {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).X = X := rfl

private theorem finite_open_reduction_eq
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (j : X ⟶ Y) [hj : IsOpenImmersion j.hom.left]
    (K : Integral C.l E X.obj.left) :
    sixFunctorIntegralOpenReduction C E m j hj K =
      (openFiniteReduction C.l E j.hom.left m).app K := by
  simp only [sixFunctorIntegralOpenReduction, openFiniteReduction, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rfl

private theorem inverse_evaluation_transport
    {A B F : Type*} [Category A] [Category B] [Category F]
    (R : A ⥤ B) (V : B ⥤ F) (T : A ⥤ F) (ρ : R ⋙ V ⟶ T)
    {U H J : A} {P : B} {Q : F} (t : U ⟶ H) (a : H ⟶ J)
    (b : P ⟶ R.obj J) [IsIso b] (v : V.obj P ⟶ Q) (q : T.obj J ⟶ Q)
    (hb : V.map b ≫ ρ.app J ≫ q = v) (d : T.obj H ⟶ Q)
    (hd : d = T.map a ≫ q) :
    V.map (R.map t ≫ R.map a ≫ inv b) ≫ v = ρ.app U ≫ T.map t ≫ d := by
  rw [hd, ← hb]
  simp only [Functor.map_comp, Category.assoc]
  rw [← V.map_comp_assoc (inv b) b, IsIso.inv_hom_id, V.map_id, Category.id_comp]
  have ha := ρ.naturality a
  have ht := ρ.naturality t
  simp only [Functor.comp_map] at ha ht
  rw [reassoc_of% ha, reassoc_of% ht]

/-- Evaluation of the open coefficient map equals the normalized finite open map.
No proper image, compact-support comparison or tensor occurs here.

Source: prop-sf-pf-coherence.proof.md, compatibility with j_!;
def-sf-operation-stages, openProjection, and the canonical open-unit scalar mate.
(blueprint: lem-sf-integral-projection-open-factor-evaluation).

Proof: expand openReduction, transporting stage.openExtension through its prescribed
functor equality. Apply the openProjection equation to its specified openRealization.
The whole-system openReduction is the inverse open-adjunction mate of reductionPull.
Evaluate that mate using OpenEvaluation.transpose and the normalized quotient/pullback
comparison. Its finite component is the inverse canonical open-unit scalar mate
sixFunctorIntegralOpenReduction, with reductionEvaluation on the input. Naturality moves
the finite open-realization comparison through the map. Thus the two scalar mates cancel,
leaving the finite coefficient comparison openExtension followed by finiteOpenExtension.
That composite, including the initial stage equality, is FactorEvaluation.extension.
Work on the simultaneous K-flat quotient construction before localization, preserving
all adjacent transitions; no faithfulness of derived evaluation is asserted. Residue Tor
and openReconstructionEffectivity justify the inverse on each constructible input.
The identity and empty open and the zero input satisfy the same mate equations. -/
theorem integralProjectionOpenFactorEvaluation
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) (m : ℕ)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (coefficientSequenceDerivedEvaluation C.l E c.Z m).map
        (ProjectionFactors.openReduction D C E n hn S hl o z f c K) ≫
      ((o.openEvaluation c.i).evaluation m).hom.app
        ((calculus C.l E X.obj.left).reduction.obj K.obj) ≫
      (sfIntrinsicExtensionByZero c.i
        (Padic.coefficientExtensionRing C.l E (m + 1))).mapDerivedCategory.map
          (((calculus C.l E X.obj.left).reductionEvaluation m).hom.app K.obj) =
    ((calculus C.l E c.Z).reductionEvaluation m).hom.app
        (((S.higher.integralExchange (identitySquare f c)).stage.openExtension.obj K).obj) ≫
      (FactorEvaluation.extension D C E n hn S f c m K).hom := by
  let := Coordinates.residueUnits hl X
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hK : finiteTorConstructibleIntegral C.l E X.obj.left K.obj := by
    rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
    exact K.property
  obtain ⟨hred, _⟩ := GeneratorReduction.openReconstructionEffectivity C.l E o
    z.realizationModel c.i K.obj (Or.inl hK)
  let := hred
  let a := (S.integralNormalization.openRealization (identitySquare f c).i
    (identitySquare f c).open_i).hom.app K
  let t := eqToHom (show
      (((S.higher.integralExchange (identitySquare f c)).stage.openExtension.obj K).obj) =
        ((S.higher.integral.openExtension (identitySquare f c).i
          (identitySquare f c).open_i).obj K).obj by
    rw [(S.higher.integralExchange (identitySquare f c)).openExtension])
  have hp : (FactorEvaluation.extensionIso D C E n hn S f c m).hom.app K =
      (scalarReductionDerivedExtension C.l E c.Z m).map a ≫
        (openFiniteReduction C.l E c.i m).app K.obj := by
    have h := eq_of_heq
      (S.integralNormalization.openProjection (identitySquare f c).i
        (identitySquare f c).open_i K m)
    simp only [finite_open_reduction_eq, identity_i_left, identity_Z_left, identity_X] at h
    simpa only [FactorEvaluation.extensionIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.comp_obj, a] using h
  have he := integralOpenFiniteEvaluation C.l E o z.realizationModel c.i K.obj m
  simp only [ProjectionFactors.openReduction, FactorEvaluation.extension,
    and_rec_eq, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Iso.app_hom]
  change (coefficientSequenceDerivedEvaluation C.l E c.Z m).map
      ((calculus C.l E c.Z).reduction.map t ≫
        (calculus C.l E c.Z).reduction.map a ≫
          inv ((z.realizationModel.openReduction C.l E c.i).app K.obj)) ≫ _ =
    ((calculus C.l E c.Z).reductionEvaluation m).hom.app _ ≫
      ((scalarReductionDerivedExtension C.l E c.Z m).map t ≫
        (FactorEvaluation.extensionIso D C E n hn S f c m).hom.app K)
  exact inverse_evaluation_transport
    (calculus C.l E c.Z).reduction (coefficientSequenceDerivedEvaluation C.l E c.Z m)
    (scalarReductionDerivedExtension C.l E c.Z m)
    ((calculus C.l E c.Z).reductionEvaluation m).hom t a
    ((z.realizationModel.openReduction C.l E c.i).app K.obj) _ _ he _ hp

end WeilConjectures.FixProjectionCompactification
