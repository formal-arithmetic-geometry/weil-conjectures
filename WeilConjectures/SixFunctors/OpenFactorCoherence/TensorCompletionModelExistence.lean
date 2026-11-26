/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel
import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorOperationUnitNormalization
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorCompletionConstruction.TensorQuotientChainData

/-! # Existence of a normalized quotient tensor model

We show that a normalized quotient-completion tensor presentation `Tensor l E X` exists.

## Implementation details

The tensor comparison is obtained by applying `integralAmbientOperationModels` to the identity
of `X` and transporting its shared operation record along `ambientPackage_eq`.

## References

* Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5
* Stacks Project, Tag 099N
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open Opposite CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

open IntegralAmbient

attribute [local implicit_reducible] PurCompactSupport.completed

open TensorCompletionConstruction

private theorem quotientChain_normalized : IsTensorChain l E X (quotientChain l E X) :=
  tensorOperationUnit_normalized l E X (quotientChain l E X) (quotientChain_app l E X)

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
private theorem comparison_exists [∀ x : X, Invertible (l : X.residueField x)] :
    ∃ β : (ordinaryModel l E X).tensor ⋙ C l E X ≅ integralCompletedTensor l E X,
      IsTensorCompletion l E X (ordinaryModel l E X) (flat_good l E X) β
        (quotientChain l E X) := by
  have hu : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
    intro x
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using (isUnit_of_invertible (l : X.residueField x)).ne_zero
  obtain ⟨F, ε, α, hF, hε, hα, hunit, ht⟩ :=
    integralAmbientOperationModels l E (𝟙 X) hu hu
  have ht' : ∃ β : modelOrdinaryTensor l E X ⋙ modelCompletion l E X ≅
      modelCompletedTensor l E X,
      ∀ P Q : (ambientGood l E X).FullSubcategory,
        (modelCompletionUnit l E X).app
            ((modelOrdinaryTensor l E X).obj
              ((modelQ l E X).obj P.obj, (modelQ l E X).obj Q.obj)) ≫
          β.hom.app ((modelQ l E X).obj P.obj, (modelQ l E X).obj Q.obj) ≫
            (modelTensorComparison l E X).hom.app (P, Q) =
          (tensorRepresentative l E X P Q).inv ≫ modelTensorUnitMap l E X P.obj Q.obj := by
    obtain ⟨β, _, hβ⟩ := ht X (Or.inl rfl)
    exact ⟨β, hβ⟩
  dsimp only [modelOrdinaryTensor, modelCompletion, modelCompletedTensor,
    modelCompletionUnit, modelQ, modelTensorComparison, tensorRepresentative,
    modelTensorModelComparison, modelTensorUnitMap, modelRoosUnit,
    modelRoos, modelTensorTowerIso, modelTotalTensor, modelGoodLocalization,
    modelTensorOnGood, modelRecordedTensorComplex, modelRecordedTensorTower,
    modelRoosComplex, modelQuotientTower] at ht'
  rw [ambientPackage_eq] at ht'
  dsimp only [rawAmbientPackage] at ht'
  obtain ⟨β, hβ⟩ := ht'
  let β' : (ordinaryModel l E X).tensor ⋙ C l E X ≅ integralCompletedTensor l E X := by
    with_unfolding_all exact β
  refine ⟨β', ?_⟩
  intro P Q hP hQ
  have h := hβ
    (by with_unfolding_all exact ⟨P, flat_good l E X P hP⟩)
    (by with_unfolding_all exact ⟨Q, flat_good l E X Q hQ⟩)
  have h' : (eta l E X).app
      ((ordinaryModel l E X).tensor.obj (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) ≫ β'.hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (integralCompletedTensorComparison l E X).hom.app
        (⟨P, flat_good l E X P hP⟩, ⟨Q, flat_good l E X Q hQ⟩) =
      ((ordinaryModel l E X).representative.app (⟨P, hP⟩, ⟨Q, hQ⟩)).inv ≫
        DerivedCategory.Q.map ((quotientChain l E X).app (P, Q)) := by
    unfold ordinaryModel quotientChain augmentTensor completionChain
    unfold ambientCompletionUnit ambientQ ambientRoosUnit ambientTotalTensor
      ambientTensorTowerIso ambientRoos at h
    unfold ambientTensorPresentation ambientTensorComparison at h
    dsimp only [AmbientTensorPresentation.ofComparison] at h
    dsimp only [Functor.isoWhiskerLeft, Functor.mapIso, Functor.whiskeringLeft,
      Functor.whiskerLeft, Functor.whiskerRight, Iso.app, ObjectProperty.ιOfLE,
      Functor.prod, NatTrans.comp_app]
    with_unfolding_all exact h
  change _ = _
  rw [h']
  exact Iso.hom_inv_id_assoc
    ((ordinaryModel l E X).representative.app (⟨P, hP⟩, ⟨Q, hQ⟩)) _

/-- A normalized quotient-completion tensor presentation exists. -/
theorem tensorCompletionModel_nonempty [CompactSpace X] [QuasiSeparatedSpace X]
    [∀ x : X, Invertible (l : X.residueField x)] :
    Nonempty (Tensor l E X) := by
  obtain ⟨β, hβ⟩ := comparison_exists l E X
  exact ⟨{ ordinary := ordinaryModel l E X
           good := flat_good l E X
           comparison := β
           chain := quotientChain l E X
           canonical := ⟨quotientChain_normalized l E X, hβ⟩ }⟩

end WeilConjectures.OpenFactorCoherence
