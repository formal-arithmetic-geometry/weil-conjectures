/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionChain
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionComparison
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedModelExistence
import all WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveQuotientAugmentations
import WeilConjectures.SixFunctors.IntegralOrdinary.OrdinaryTensorRingedModelComparison
import WeilConjectures.SixFunctors.IntegralOrdinary.TensorCompletionChainRingedIdentification
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Mathlib.CategoryTheory.Localization.Prod

/-! # Tensor augmentation and coherent reduction

Source: fix-prop-projection-formula.proof.md, integral reconstruction;
Stacks 07A4 and 0941. This square involves the forward augmentation maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified signed total tensor, restricted to the flat-term K-flat models.
Source: Stacks 07A4
(blueprint: lem-sf-tensor-reduction-augmentation). -/
@[reducible] def tensorModel (X : Scheme.{u}) :
    ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X) where
  tensor := ConstructibleTensorModel.ordinaryTensor l E X
  representative := by
    let i : (proEtaleFlatRepresentatives X
        ((PurCompactSupport.completed l E).ring X)).FullSubcategory ⥤
        (integralOperationsGoodComplex l E X).FullSubcategory :=
      ObjectProperty.ιOfLE (fun P hP ↦
        ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1, hP.2⟩)
    with_unfolding_all
      exact Functor.isoWhiskerLeft (i.prod i)
        (ConstructibleTensorModel.tensorRepresentativeIso l E X)

/-- The forward tensor augmentation is fixed on entire flat-term K-flat representatives.
Source: Bhatt--Scholze, Definition 3.4.10; Stacks 0941
(blueprint: lem-sf-tensor-reduction-augmentation). -/
def TensorAugmentationNormalized (X : Scheme.{u})
    (τ : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E X).FullSubcategory,
    (ConstructibleTensorModel.tensorRepresentativeIso l E X).hom.app (P, Q) ≫
        τ.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (P, Q) =
      DerivedCategory.Q.map
        ((ConstructibleTensorModel.tensorCompletionChain l E X).app (P.obj, Q.obj))

attribute [local implicit_reducible] PurCompactSupport.completed
  integralOperationsGoodLocalization integralOperationsTensorOnGood
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  pullbackTensorCalculus pullbackTensorIntegralTensorModel integralCompletedTensorComparison
  coefficientSequenceLimit

/-- Coherent reduction of ordinary tensor is strong monoidal, with its adjunct fixed
by the specified strict tensor augmentation. This assertion involves one scheme and
no geometric inverse image or tensor/pullback comparison.

Source: Stacks 07A4 and 0941; Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5.
(blueprint: lem-sf-tensor-reduction-augmentation).

Proof: compare the ordinary tensor model with the integral tensor model of the
coherent calculus using their signed total tensors on simultaneous flat K-flat
representatives. Compose this comparison with the calculus reductionTensor. Both
comparisons are isomorphisms. The ordinary scalar extension unit sends a section x
to 1 tensor x. The normalized scalar tensor map sends 1 tensor (x tensor y) to
(1 tensor x) tensor (1 tensor y), with the same quotient transitions. Its adjunct
under reduction/limit is the strict Roos map with these product components and zero
shifted component. The full Roos model normalization identifies its target with
pullbackTensorIntegralTensorModel. Thus its adjunct is every normalized tensor
augmentation. Faithfulness of product good-complex localization proves this for
all derived pairs. Such an augmentation exists by tensorCompletionComparison.
The reduction/limit Hom bijection and that augmentation determine every component
of the comparison, so it is unique. Zero complexes and the empty scheme use the
same unit and totalization equations. -/
theorem tensorReductionAugmentation_exists (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    ∃ b : (tensorModel l E X).tensor ⋙ (pullbackTensorCalculus l E X).reduction ≅
        ((pullbackTensorCalculus l E X).reduction.prod
          (pullbackTensorCalculus l E X).reduction) ⋙
            (pullbackTensorCalculus l E X).systemClosed.tensor,
      ∀ (τ : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X),
        TensorAugmentationNormalized l E X τ →
        ∀ M N : DerivedCategory (integralTowerModules l E X),
          τ.app (M, N) ≫ (pullbackTensorIntegralTensorModel l E X).hom.app (M, N) =
            (pullbackTensorCalculus l E X).adjunction.unit.app
                ((tensorModel l E X).tensor.obj (M, N)) ≫
              (coefficientSequenceLimit l E X).map (b.hom.app (M, N)) := by
  obtain ⟨d, _⟩ := IntegralSystemRealization.integralRingedModelExistence l E
  obtain ⟨e, he⟩ := tensorRingedModelComparison l E X d
  let S := pullbackTensorCalculus l E X
  let R := coefficientSequenceLimit l E X
  let b : (tensorModel l E X).tensor ⋙ S.reduction ≅
      S.reduction.prod S.reduction ⋙ S.systemClosed.tensor :=
    Functor.isoWhiskerRight (e ≪≫ eqToIso (d.tensorClosed X)) S.reduction ≪≫ S.reductionTensor
  let τ₀ : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X :=
    e.hom ≫ (d.tensor X).chi l E
  have hτ₀ : TensorAugmentationNormalized l E X τ₀ := by
    intro P Q
    have hc := (d.tensor X).canonical.2 P.obj Q.obj P.property Q.property
    rw [ringedTensorChain_eq_tensorCompletionChain l E X d P.obj Q.obj] at hc
    have hh := congrArg (fun z ↦ z ≫
      ((d.tensor X).chi l E).app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (P, Q)) (he P Q)
    calc
      _ = (d.tensor X).ordinary.representative.hom.app
          (⟨P.obj, P.property⟩, ⟨Q.obj, Q.property⟩) ≫
          ((d.tensor X).chi l E).app
            (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
            (integralCompletedTensorComparison l E X).hom.app (P, Q) := by
        simpa only [τ₀, NatTrans.comp_app, Category.assoc] using hh
      _ = _ := by
        simpa only [OpenFactorCoherence.Tensor.chi, NatTrans.comp_app,
          Functor.whiskerLeft_app, Category.assoc] using hc
  let q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  have hu (τ : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X)
      (hτ : TensorAugmentationNormalized l E X τ) : τ = τ₀ := by
    apply Localization.natTrans_ext (q.prod q) (W.prod W)
    rintro ⟨P, Q⟩
    change τ.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      τ₀.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
    apply (cancel_epi
      ((ConstructibleTensorModel.tensorRepresentativeIso l E X).hom.app (P, Q))).1
    apply (cancel_mono ((integralCompletedTensorComparison l E X).hom.app (P, Q))).1
    simpa only [Category.assoc] using (hτ P Q).trans (hτ₀ P Q).symm
  let α := τ₀ ≫ (pullbackTensorIntegralTensorModel l E X).hom
  let β := Functor.whiskerLeft (tensorModel l E X).tensor S.adjunction.unit ≫
    Functor.whiskerRight b.hom R
  have hab : α = β := by
    apply Localization.natTrans_ext (q.prod q) (W.prod W)
    rintro ⟨P, Q⟩
    have ha := GeneratorReduction.tensor_augmentation_onGood l E d X P Q
    have hn := S.adjunction.unit.naturality
      (e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    dsimp only [α, τ₀, NatTrans.comp_app]
    rw [Category.assoc]
    change e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      (((d.tensor X).chi l E).app _ ≫
        (pullbackTensorIntegralTensorModel l E X).hom.app _) = _
    rw [ha, ← Category.assoc, hn, Category.assoc]
    simp only [β, b, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      eqToIso.hom, eqToHom_app, Functor.map_comp, Category.assoc,
      q, R, S, integralOperationsGoodLocalization, Functor.prod_obj, Functor.comp_obj,
      ObjectProperty.ι_obj]
  refine ⟨b, ?_⟩
  intro τ hτ M N
  rw [hu τ hτ]
  exact congrArg (fun t ↦ t.app (M, N)) hab

/-- The adjunction Hom bijection makes the normalized reduction comparison unique.
Source: Stacks 07A6; the reduction/limit adjunction
(blueprint: lem-sf-tensor-reduction-augmentation). -/
theorem tensorReductionAugmentation_existsUnique (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    ∃! b : (tensorModel l E X).tensor ⋙ (pullbackTensorCalculus l E X).reduction ≅
        ((pullbackTensorCalculus l E X).reduction.prod
          (pullbackTensorCalculus l E X).reduction) ⋙
            (pullbackTensorCalculus l E X).systemClosed.tensor,
      ∀ (τ : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X),
        TensorAugmentationNormalized l E X τ →
        ∀ M N : DerivedCategory (integralTowerModules l E X),
          τ.app (M, N) ≫ (pullbackTensorIntegralTensorModel l E X).hom.app (M, N) =
            (pullbackTensorCalculus l E X).adjunction.unit.app
                ((tensorModel l E X).tensor.obj (M, N)) ≫
              (coefficientSequenceLimit l E X).map (b.hom.app (M, N)) := by
  obtain ⟨b, hb⟩ := tensorReductionAugmentation_exists l E X
  refine ⟨b, hb, ?_⟩
  intro c hc
  obtain ⟨τ, hτ, _⟩ := ConstructibleTensorModel.tensorCompletionComparison l E X
  have hτ' : TensorAugmentationNormalized l E X τ := hτ
  apply Iso.ext
  apply NatTrans.ext
  funext MN
  rcases MN with ⟨M, N⟩
  apply ((pullbackTensorCalculus l E X).adjunction.homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit] using
    (hc τ hτ' M N).symm.trans (hb τ hτ' M N)

/-- The unique strong reduction comparison with the strict augmentation normalization.
Source: Stacks 07A4 and 0941 (blueprint: lem-sf-tensor-reduction-augmentation). -/
def tensorReductionComparison (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :=
  (tensorReductionAugmentation_existsUnique l E X).exists.choose

end WeilConjectures.IntegralOrdinary
