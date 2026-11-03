/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionDescentSystem
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionDescentSystem
import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionGoodRepresentativeSquare
import all WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeModels
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
public import WeilConjectures.PoincareDuality.Pod.Reduction.PodReductionRepresentativeAssembly
public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensor
public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexUnaryModel
public import WeilConjectures.SixFunctors.Coefficient.CoefficientReductionTensorEvaluationPasting
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictDerivedSquare
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Descent of the strict reduction/tensor representative square

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent)
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance 1000000] SheafOfModules.instAbelian

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh CoefficientClosedStructure.tensor
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
  pullbackTensorReductionModel pullbackTensorSystemModel
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  derivedInternalHomOfUniverses coefficientSequenceCommRingSheaf
  pullbackTensorSequenceInverse integralComparisonSequencePullback
  pullbackTensorSystemComparison PodReductionRepresentatives.systemChain
attribute [local implicit_reducible] CategoryTheory.uniformProd
  CategoryTheory.prod CategoryTheory.prod'
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  coefficientIntegralInternalHom coefficientSequenceInternalHom coefficientFiniteInternalHom
  podReindexCalculus pullbackTensorCalculus
  integralTowerHasDerivedCategory coefficientSequenceHasDerived
  pullbackTensorSequenceDerived
  integralComparisonDerivedSequencePullback

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 10000000] HasDerivedCategory.standard
attribute [local irreducible] PodReductionRepresentatives.factor
set_option allowUnsafeReducibility true in
attribute [local irreducible] podReindexingDerivedFunctor podReindexingDerivedFactors
open PodReindexingCoherence
attribute [local irreducible] Scheme.residueField

private theorem reduction_square_transport
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (R : C ⥤ A) (S : D ⥤ B) (F : C ⥤ D) (G : A ⥤ B)
    (T : C × C ⥤ C) (W : D × D ⥤ D)
    (U : A × A ⥤ A) (V : B × B ⥤ B)
    (a : R ⋙ G ⟶ F ⋙ S) (v : T ⋙ F ⟶ F.prod F ⋙ W)
    (w : U ⋙ G ⟶ G.prod G ⋙ V)
    (τ : T ⋙ R ⟶ R.prod R ⋙ U) (σ : W ⋙ S ⟶ S.prod S ⋙ V)
    {P Q M N : C} (eP : P ≅ M) (eQ : Q ≅ N)
    (hg : G.map (τ.app (P, Q)) ≫ w.app (R.obj P, R.obj Q) ≫
        V.map (Prod.mkHom (a.app P) (a.app Q)) =
      a.app (T.obj (P, Q)) ≫ S.map (v.app (P, Q)) ≫
        σ.app (F.obj P, F.obj Q)) :
    G.map (τ.app (M, N)) ≫ w.app (R.obj M, R.obj N) ≫
        V.map (Prod.mkHom (a.app M) (a.app N)) =
      a.app (T.obj (M, N)) ≫ S.map (v.app (M, N)) ≫
        σ.app (F.obj M, F.obj N) := by
  have hv := v.naturality (eP.prod eQ).hom
  have ht := τ.naturality (eP.prod eQ).hom
  dsimp only [Functor.comp, Functor.prod, Iso.prod, Prod.mkHom] at ht hv
  have hgt := congrArg (fun z ↦ G.map z) ht
  simp only [Functor.map_comp] at hgt
  have hw := w.naturality (Prod.mkHom (R.map eP.hom) (R.map eQ.hom))
  simp only [Functor.comp_map, Functor.prod_map] at hw
  have ha := a.naturality (T.map (eP.prod eQ).hom)
  dsimp only [Functor.comp, Iso.prod, Prod.mkHom] at ha
  have hs := σ.naturality (Prod.mkHom (F.map eP.hom) (F.map eQ.hom))
  simp only [Functor.comp_map, Functor.prod_map] at hs
  have hsv := congrArg (fun z ↦ S.map z) hv
  simp only [Functor.map_comp] at hsv
  apply (cancel_epi (G.map (R.map (T.map (eP.prod eQ).hom)))).1
  simp only [Iso.prod_hom, Prod.mkHom]
  rw [reassoc_of% hgt, reassoc_of% hw]
  rw [tensor_comp]
  have hp := a.naturality eP.hom
  have hq := a.naturality eQ.hom
  dsimp only [Functor.comp] at hp hq
  rw [hp, hq]
  rw [← tensor_comp]
  rw [reassoc_of% ha, reassoc_of% hsv, hs]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ V.map (Prod.mkHom
      (S.map (F.map eP.hom)) (S.map (F.map eQ.hom)))) hg

private theorem podReduction_representative_square_legacy
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g)
    (hA : PodCompletionReindex.Laws l E g A)
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (hPure : ∀ (P L : PodReindexingCoherence.K l E Y none) (p q k : ℤ)
      (hk : p + q = k) (U : X.ProEt)
      (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (L.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((c.tensorChain P L).hom.f k).val.app (op U))
        (coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology Y) (podReindexingRing l E Y none) P L p q k hk
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u}
        (ProEt.topology X) (podReindexingRing l E X none)
        ((podReindexingComplexFunctor l E g none).obj P)
        ((podReindexingComplexFunctor l E g none).obj L) p q k hk
        (op U) x y)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralComparisonDerivedSequencePullback l E g).map
        ((podReindexCalculus l E Y).reductionTensor.hom.app ((podReindexingQ l E Y none).obj P.obj,
          (podReindexingQ l E Y none).obj Q.obj)) ≫
      (podReindexingSystemTensor l E g).hom.app
        ((podReindexCalculus l E Y).reduction.obj ((podReindexingQ l E Y none).obj P.obj),
          (podReindexCalculus l E Y).reduction.obj ((podReindexingQ l E Y none).obj Q.obj)) ≫
      (podReindexCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          (A.reduction.hom.app ((podReindexingQ l E Y none).obj P.obj))
          (A.reduction.hom.app ((podReindexingQ l E Y none).obj Q.obj))) =
    A.reduction.hom.app
        ((podReindexCalculus l E Y).integralClosed.tensor.obj
          ((podReindexingQ l E Y none).obj P.obj,
          (podReindexingQ l E Y none).obj Q.obj)) ≫
      (podReindexCalculus l E X).reduction.map
        ((reductionOrdinaryTensor l E g c h).hom.app
          ((podReindexingQ l E Y none).obj P.obj, (podReindexingQ l E Y none).obj Q.obj)) ≫
      (podReindexCalculus l E X).reductionTensor.hom.app
        ((podOrdinaryReindex l E g).obj ((podReindexingQ l E Y none).obj P.obj),
          (podOrdinaryReindex l E g).obj ((podReindexingQ l E Y none).obj Q.obj)) := by
  let T0 := (PodReindexingCoherence.total l E Y none).obj (P.obj, Q.obj)
  have hT := total_good l E Y P Q
  obtain ⟨hFP, βP, hβP, hUP⟩ := PodReductionRepresentatives.unary_model l E g A hA h P
  obtain ⟨hFQ, βQ, hβQ, hUQ⟩ := PodReductionRepresentatives.unary_model l E g A hA h Q
  obtain ⟨hFT, βT, hβT, hUT⟩ := PodReductionRepresentatives.unary_model l E g A hA h ⟨T0, hT⟩
  let CY := podReindexCalculus l E Y
  let CX := podReindexCalculus l E X
  let G := integralComparisonDerivedSequencePullback l E g
  let D := podOrdinaryReindex l E g
  let T0 := (T[Y]).obj (P.obj, Q.obj)
  let FP : (integralOperationsGoodComplex l E X).FullSubcategory := ⟨_, hFP⟩
  let FQ : (integralOperationsGoodComplex l E X).FullSubcategory := ⟨_, hFQ⟩
  let FT : (integralOperationsGoodComplex l E X).FullSubcategory := ⟨_, hFT⟩
  let TX := (T[X]).obj (FP.obj, FQ.obj)
  let hTX := total_good l E X FP FQ
  let bY := ordinaryModel l E Y CY.integralClosed CY.integralTensorModel
    P.obj Q.obj P.property.1 Q.property.1
  let bX := ordinaryModel l E X CX.integralClosed CX.integralTensorModel
    FP.obj FQ.obj hFP.1 hFQ.1
  let fP := (factor l E g h).app P.obj
  let fQ := (factor l E g h).app Q.obj
  let fT := (factor l E g h).app T0
  let rP := (pullbackTensorReductionModel l E Y).app P
  let rQ := (pullbackTensorReductionModel l E Y).app Q
  let rT := (pullbackTensorReductionModel l E Y).app ⟨T0, hT⟩
  let rFP := (pullbackTensorReductionModel l E X).app FP
  let rFQ := (pullbackTensorReductionModel l E X).app FQ
  let rFT := (pullbackTensorReductionModel l E X).app FT
  let rTX := (pullbackTensorReductionModel l E X).app ⟨TX, hTX⟩
  let RP := (R[Y]).obj P.obj
  let RQ := (R[Y]).obj Q.obj
  let sY := systemModel l E Y RP RQ
    (pullbackTensorReductionGood l E Y P) (pullbackTensorReductionGood l E Y Q)
  let sX := systemModel l E X _ _
    (pullbackTensorReductionGood l E X FP) (pullbackTensorReductionGood l E X FQ)
  let iP := (systemFactor l E g).hom.app RP
  let iQ := (systemFactor l E g).hom.app RQ
  let iT := (systemFactor l E g).hom.app
    ((R[Y]).obj T0)
  let iS := (systemFactor l E g).hom.app
    ((S[Y]).obj (RP, RQ))
  let ψY := tensorReductionStrictMap l E Y P.obj Q.obj
  let ψX := tensorReductionStrictMap l E X FP.obj FQ.obj
  let t := c.tensorChain P.obj Q.obj
  let w := podReindexingSystemTensor l E g
  let hIP := sequence_good l E g RP (pullbackTensorReductionGood l E Y P)
  let hIQ := sequence_good l E g RQ (pullbackTensorReductionGood l E Y Q)
  have hS := system_model l E g RP RQ
    (pullbackTensorReductionGood l E Y P) (pullbackTensorReductionGood l E Y Q) hIP hIQ
  let sI := systemModel l E X _ _ hIP hIQ
  have hY := reduction_model l E Y P Q hT
  have hX := reduction_model l E X FP FQ hTX
  have hO := ordinary_model l E g c h P Q hFP hFQ
  have hN := system_naturality l E X _ _ _ _ hIP hIQ
    (pullbackTensorReductionGood l E X FP) (pullbackTensorReductionGood l E X FQ)
    βP.hom βQ.hom
  have hi := (systemFactor l E g).hom.naturality
    ψY
  have hr := (pullbackTensorReductionModel l E X).hom.naturality
    (X := FT) (Y := ⟨TX, hTX⟩) (ObjectProperty.homMk t.hom)
  have hc := strict_tensor l E g P.obj Q.obj t (hPure P.obj Q.obj)
    βP βQ βT hβP hβQ hβT
  have hc' := map_three (systemQ l E X) hc
  exact podReduction_assemble_representative CY.reduction CX.reduction D G
    CY.integralClosed.tensor CX.integralClosed.tensor
    CY.systemClosed.tensor CX.systemClosed.tensor
    A.reduction.hom (reductionOrdinaryTensor l E g c h).hom w.hom
    CY.reductionTensor.hom CX.reductionTensor.hom
    ((podReindexingQ l E Y none).obj P.obj) ((podReindexingQ l E Y none).obj Q.obj)
    ((podReindexingQ l E Y none).obj T0) ((podReindexingQ l E X none).obj FP.obj)
    ((podReindexingQ l E X none).obj FQ.obj) ((podReindexingQ l E X none).obj FT.obj)
    ((podReindexingQ l E X none).obj TX) bY bX fP fQ fT
    ((systemQ l E Y).obj RP) ((systemQ l E Y).obj RQ)
    ((systemQ l E Y).obj ((R[Y]).obj T0))
    ((systemQ l E Y).obj ((S[Y]).obj (RP, RQ)))
    ((systemQ l E X).obj ((I[g]).obj RP)) ((systemQ l E X).obj ((I[g]).obj RQ))
    ((systemQ l E X).obj ((I[g]).obj ((R[Y]).obj T0)))
    ((systemQ l E X).obj ((I[g]).obj ((S[Y]).obj (RP, RQ))))
    ((systemQ l E X).obj ((S[X]).obj (((I[g]).obj RP, (I[g]).obj RQ))))
    ((systemQ l E X).obj ((R[X]).obj FP.obj))
    ((systemQ l E X).obj ((R[X]).obj FQ.obj))
    ((systemQ l E X).obj ((R[X]).obj FT.obj))
    ((systemQ l E X).obj ((R[X]).obj TX))
    ((systemQ l E X).obj ((S[X]).obj (((R[X]).obj FP.obj, (R[X]).obj FQ.obj))))
    rP rQ rT rFP rFQ rFT rTX sY sI sX iP iQ iT iS
    ((systemQ l E Y).map ψY) ((systemQ l E X).map ((I[g]).map ψY))
    ((systemQ l E X).map ((systemChain l E g).hom.app (RP, RQ)))
    ((systemQ l E X).map βP.hom) ((systemQ l E X).map βQ.hom)
    ((systemQ l E X).map βT.hom)
    ((systemQ l E X).map ((S[X]).map (Prod.mkHom βP.hom βQ.hom)))
    ((podReindexingQ l E X none).map t.hom) ((systemQ l E X).map ((R[X]).map t.hom))
    ((systemQ l E X).map ψX) hUP hUQ hUT hY hX hO hS hN hi hr hc'

/--
STATEMENT-DISPUTED: The former statement quantified over arbitrary `w` and `v`,
although no compatibility laws related them to the canonical comparisons were assumed.
The corrected statement uses the canonical normalized system comparison and ordinary
tensor map.

The strict pure-tensor calculation descends through the two K-flat localizations.
The hypothesis is the comparison's sectionwise pure-tensor formula; the conclusion
is the whole-system square after the reduction and system tensor maps.  The descent
uses the quotient-generator and transition laws of `A`, the normalized system
comparison, and full faithfulness of the product localization.  It is stated
separately so that the representative calculation is not hidden in the derived
square theorem.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent).
-/
theorem podReindexing_reduction_tensor_square_descent
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g)
    (hA : PodCompletionReindex.Laws l E g A)
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (hPure : ∀ (P L : PodReindexingCoherence.K l E Y none) (p q k : ℤ)
      (hk : p + q = k) (U : X.ProEt)
      (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (L.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((c.tensorChain P L).hom.f k).val.app (op U))
        (coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology Y) (podReindexingRing l E Y none) P L p q k hk
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u}
        (ProEt.topology X) (podReindexingRing l E X none)
        ((podReindexingComplexFunctor l E g none).obj P)
        ((podReindexingComplexFunctor l E g none).obj L) p q k hk
        (op U) x y)
    (M N : podReindexingDerived l E Y none) :
    (integralComparisonDerivedSequencePullback l E g).map
        ((podReindexCalculus l E Y).reductionTensor.hom.app (M, N)) ≫
      (podReindexingSystemTensor l E g).hom.app
        ((podReindexCalculus l E Y).reduction.obj M,
          (podReindexCalculus l E Y).reduction.obj N) ≫
      (podReindexCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (A.reduction.hom.app M) (A.reduction.hom.app N)) =
    A.reduction.hom.app
        ((podReindexCalculus l E Y).integralClosed.tensor.obj (M, N)) ≫
      (podReindexCalculus l E X).reduction.map
        (podReindexingIntegralTensorHom l E g c h M N) ≫
      (podReindexCalculus l E X).reductionTensor.hom.app
        ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj N) := by
  obtain ⟨P, ⟨eP⟩⟩ := good_representative l E Y M
  obtain ⟨Q, ⟨eQ⟩⟩ := good_representative l E Y N
  have hg := podReduction_representative_square_legacy l E g A hA c h hPure P Q
  have result := reduction_square_transport
    (podReindexCalculus l E Y).reduction (podReindexCalculus l E X).reduction
    (podOrdinaryReindex l E g) (integralComparisonDerivedSequencePullback l E g)
    (podReindexCalculus l E Y).integralClosed.tensor
    (podReindexCalculus l E X).integralClosed.tensor
    (podReindexCalculus l E Y).systemClosed.tensor
    (podReindexCalculus l E X).systemClosed.tensor
    A.reduction.hom (reductionOrdinaryTensor l E g c h).hom
    (podReindexingSystemTensor l E g).hom
    (podReindexCalculus l E Y).reductionTensor.hom
    (podReindexCalculus l E X).reductionTensor.hom eP eQ hg
  simpa only [reductionOrdinaryTensor_hom] using result

end WeilConjectures
