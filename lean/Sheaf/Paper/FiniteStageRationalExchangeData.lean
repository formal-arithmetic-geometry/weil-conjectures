/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q39 and Y9
-/
module

public import Sheaf.Paper.AmbientCompleteCoefficientCategories
public import Sheaf.Paper.ECoefficientSmoothBaseChange
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Sheaf.CategoryTheory.StageSystemFunctorDescent

/-! # Data for finite-stage rational exchange coherence

These are the unchanged raw operations and coherence predicates used by
`FiniteStageRationalExchangeCoherence`. The raw-only predicate isolates the
coefficient construction before the supported Karoubi extension.
(blueprint: def-sbc-finite-stage-rational-exchange-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteStageRationalExchange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The raw extension of the actual integral completed pullback.
Source: sketch32, lines 1218--1228
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence). -/
abbrev rawPull (E : Padic.FiniteCoefficientFields l Ω)
    {U V : Scheme.{u}} (q : U ⟶ V) :=
  ScalarLocalization.between (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcUniformizer l (pbcFiniteField.{u} l Ω E))
    (sbcPull l (pbcFiniteField.{u} l Ω E) q)

/-- The raw extension of the actual integral derived direct image.
Source: sketch32, lines 1218--1228
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence). -/
abbrev rawPush (E : Padic.FiniteCoefficientFields l Ω)
    {U V : Scheme.{u}} (q : U ⟶ V) :=
  ScalarLocalization.between (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcUniformizer l (pbcFiniteField.{u} l Ω E))
    (sbcPush l (pbcFiniteField.{u} l Ω E) q)

section Operations

variable {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [iV : Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
  (q : U ⟶ V)

/-- The integral and raw clauses of operation coherence, before Karoubi extension.
Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-raw-operation-coherence). -/
def HasRawOperationCoherence
    (pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
        pbcAmbientCompleteIntegralTransition l Ω V a ≅
      pbcAmbientCompleteIntegralTransition l Ω U a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) q)
    (pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
        pbcAmbientCompleteIntegralTransition l Ω U a ≅
      pbcAmbientCompleteIntegralTransition l Ω V a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) q)
    (rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω U)
    (pbcAmbientCompleteRawSystem l Ω V))
    (rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω V)
    (pbcAmbientCompleteRawSystem l Ω U))
    : Prop :=
  ∃ (integral_tensorU_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    pbcAmbientScalarExtension l Ω U a =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U),
  ∃ (integral_tensorV_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    pbcAmbientScalarExtension l Ω V a =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) V),
  ∃ (integral_pushModel : ∀ E : Padic.FiniteCoefficientFields l Ω,
    sbcAmbientPush l (pbcFiniteField.{u} l Ω E) q ≅
      pbcActualDerivedPush q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E))),
  ∃ (_integral_pushModel_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω), integral_pushModel E =
      (conjugateIsoEquiv
            (proEtaleRingDerivedAdjunction q
              (pbcAdicCompletion V (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
              (pbcAdicCompletion U (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
              (sbcCoefficientIso l (pbcFiniteField.{u} l Ω E) q))
            (pbcActualDerivedAdjunction q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
            (sbcOrdinaryDerivedIso l (pbcFiniteField.{u} l Ω E) q))),
  ∃ (integral_pullModel : ∀ E : Padic.FiniteCoefficientFields l Ω,
    sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
        ObjectProperty.ι (IsPbcComplete l (pbcFiniteField.{u} l Ω E) U) ≅
      ObjectProperty.ι (IsPbcComplete l (pbcFiniteField.{u} l Ω E) V) ⋙
        pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E))),
  ∃ (_integral_pullModel_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω), integral_pullModel E =
      (Functor.isoWhiskerLeft
            (ObjectProperty.ι (IsPbcComplete l (pbcFiniteField.{u} l Ω E) V))
            (Functor.associator
              (completedReductionTower V (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
              (completedTowerPullback q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
              (completedTowerRlim (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)) U)).symm ≪≫
          (pbcActualCompletedPullback_tower
            (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)) q).exists.choose)),
  ∃ (_integral_integralPush_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) U),
    HEq ((pPush a).hom.app K).hom
      ((eqToIso (integral_tensorV_eq a)).hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj
          K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
          (pbcFiniteFieldInclusion l Ω a) V).map
          ((integral_pushModel E).hom.app K.obj) ≫
        (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
          (pbcFiniteFieldInclusion l Ω a) q).hom.app K.obj ≫
        (integral_pushModel M).inv.app
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
            (pbcFiniteFieldInclusion l Ω a) U).obj K.obj) ≫
        (sbcAmbientPush l (pbcFiniteField.{u} l Ω M) q).map
          ((eqToIso (integral_tensorU_eq a)).inv.app K.obj))),
  ∃ (_integral_integralPull_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) V),
    HEq ((pPull a).hom.app K).hom
      ((eqToIso (integral_tensorU_eq a)).hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj
          K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
          (pbcFiniteFieldInclusion l Ω a) U).map
          ((integral_pullModel E).hom.app K) ≫
        (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
          (pbcFiniteFieldInclusion l Ω a) q).inv.app K.obj ≫
        (pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω M))).map
          ((eqToIso (integral_tensorV_eq a)).inv.app K.obj) ≫
        (integral_pullModel M).inv.app
          (⟨(pbcAmbientScalarExtension l Ω V a).obj K.obj,
            pbcAmbientCompleteTensor_preserves l Ω V a K⟩))),
  ∃ (_integral_integralPush_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) U),
    (pPush (le_refl E)).hom.app K ≫
        (sbcPush l (pbcFiniteField.{u} l Ω E) q).map
          ((pbcAmbientCompleteIntegralUnit l Ω U E).hom.app K) =
      (pbcAmbientCompleteIntegralUnit l Ω V E).hom.app
        ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K)),
  ∃ (_integral_integralPull_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) V),
    (pPull (le_refl E)).hom.app K ≫
        (sbcPull l (pbcFiniteField.{u} l Ω E) q).map
          ((pbcAmbientCompleteIntegralUnit l Ω V E).hom.app K) =
      (pbcAmbientCompleteIntegralUnit l Ω U E).hom.app
        ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K)),
  ∃ (_raw_rawPush_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    rPush.Φ E = FiniteStageRationalExchange.rawPush l Ω E q),
  ∃ (_raw_rawPush_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (rPush.Φ E).Additive),
  ∃ (_raw_rawPush_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (rPush.β (le_refl E)) (Iso.refl (rPush.Φ E))),
  ∃ (_raw_rawPush_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) U),
    HEq ((rPush.β a).hom.app ((pbcAmbientCompleteLocalization l Ω U E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω V a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K) ≫
        (pbcAmbientCompleteLocalization l Ω V M).map ((pPush a).hom.app K) ≫
        (FiniteStageRationalExchange.rawPush l Ω M q).map
          ((pbcAmbientCompleteIntegralComparison l Ω U a).inv.app K))),
  ∃ (_raw_rawPull_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    rPull.Φ E = FiniteStageRationalExchange.rawPull l Ω E q),
  ∃ (_raw_rawPull_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (rPull.Φ E).Additive),
  ∃ (_raw_rawPull_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (rPull.β (le_refl E)) (Iso.refl (rPull.Φ E))),
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) V),
    HEq ((rPull.β a).hom.app ((pbcAmbientCompleteLocalization l Ω V E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω U a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K) ≫
        (pbcAmbientCompleteLocalization l Ω U M).map ((pPull a).hom.app K) ≫
        (FiniteStageRationalExchange.rawPull l Ω M q).map
          ((pbcAmbientCompleteIntegralComparison l Ω V a).inv.app K))

/-- Operation coherence with its four data exposed for the composite comparison formulas.
All canonical integral normalizations, raw and Karoubi units, and tower clauses
are conclusions of the proposition. No comparison is chosen from a mere existence proof.
Source: sketch32, lines 1218--1228 and 1291--1321
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence). -/
def HasOperationCoherence
    (pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
        pbcAmbientCompleteIntegralTransition l Ω V a ≅
      pbcAmbientCompleteIntegralTransition l Ω U a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) q)
    (pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
        pbcAmbientCompleteIntegralTransition l Ω U a ≅
      pbcAmbientCompleteIntegralTransition l Ω V a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) q)
    (rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω U)
    (pbcAmbientCompleteRawSystem l Ω V))
    (rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω V)
    (pbcAmbientCompleteRawSystem l Ω U))
    : Prop :=
  ∃ (integral_tensorU_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    pbcAmbientScalarExtension l Ω U a =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U),
  ∃ (integral_tensorV_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    pbcAmbientScalarExtension l Ω V a =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) V),
  ∃ (integral_pushModel : ∀ E : Padic.FiniteCoefficientFields l Ω,
    sbcAmbientPush l (pbcFiniteField.{u} l Ω E) q ≅
      pbcActualDerivedPush q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E))),
  ∃ (_integral_pushModel_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω), integral_pushModel E =
      (conjugateIsoEquiv
            (proEtaleRingDerivedAdjunction q
              (pbcAdicCompletion V (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
              (pbcAdicCompletion U (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
              (sbcCoefficientIso l (pbcFiniteField.{u} l Ω E) q))
            (pbcActualDerivedAdjunction q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
            (sbcOrdinaryDerivedIso l (pbcFiniteField.{u} l Ω E) q))),
  ∃ (integral_pullModel : ∀ E : Padic.FiniteCoefficientFields l Ω,
    sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
        ObjectProperty.ι (IsPbcComplete l (pbcFiniteField.{u} l Ω E) U) ≅
      ObjectProperty.ι (IsPbcComplete l (pbcFiniteField.{u} l Ω E) V) ⋙
        pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E))),
  ∃ (_integral_pullModel_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω), integral_pullModel E =
      (Functor.isoWhiskerLeft
            (ObjectProperty.ι (IsPbcComplete l (pbcFiniteField.{u} l Ω E) V))
            (Functor.associator
              (completedReductionTower V (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
              (completedTowerPullback q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)))
              (completedTowerRlim (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)) U)).symm ≪≫
          (pbcActualCompletedPullback_tower
            (pbcIntegralDatum l (pbcFiniteField.{u} l Ω E)) q).exists.choose)),
  ∃ (_integral_integralPush_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) U),
    HEq ((pPush a).hom.app K).hom
      ((eqToIso (integral_tensorV_eq a)).hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj
          K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
          (pbcFiniteFieldInclusion l Ω a) V).map
          ((integral_pushModel E).hom.app K.obj) ≫
        (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
          (pbcFiniteFieldInclusion l Ω a) q).hom.app K.obj ≫
        (integral_pushModel M).inv.app
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
            (pbcFiniteFieldInclusion l Ω a) U).obj K.obj) ≫
        (sbcAmbientPush l (pbcFiniteField.{u} l Ω M) q).map
          ((eqToIso (integral_tensorU_eq a)).inv.app K.obj))),
  ∃ (_integral_integralPull_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) V),
    HEq ((pPull a).hom.app K).hom
      ((eqToIso (integral_tensorU_eq a)).hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj
          K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
          (pbcFiniteFieldInclusion l Ω a) U).map
          ((integral_pullModel E).hom.app K) ≫
        (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
          (pbcFiniteFieldInclusion l Ω a) q).inv.app K.obj ≫
        (pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω M))).map
          ((eqToIso (integral_tensorV_eq a)).inv.app K.obj) ≫
        (integral_pullModel M).inv.app
          (⟨(pbcAmbientScalarExtension l Ω V a).obj K.obj,
            pbcAmbientCompleteTensor_preserves l Ω V a K⟩))),
  ∃ (_integral_integralPush_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) U),
    (pPush (le_refl E)).hom.app K ≫
        (sbcPush l (pbcFiniteField.{u} l Ω E) q).map
          ((pbcAmbientCompleteIntegralUnit l Ω U E).hom.app K) =
      (pbcAmbientCompleteIntegralUnit l Ω V E).hom.app
        ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K)),
  ∃ (_integral_integralPull_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) V),
    (pPull (le_refl E)).hom.app K ≫
        (sbcPull l (pbcFiniteField.{u} l Ω E) q).map
          ((pbcAmbientCompleteIntegralUnit l Ω V E).hom.app K) =
      (pbcAmbientCompleteIntegralUnit l Ω U E).hom.app
        ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K)),
  ∃ (_raw_rawPush_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    rPush.Φ E = FiniteStageRationalExchange.rawPush l Ω E q),
  ∃ (_raw_rawPush_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (rPush.Φ E).Additive),
  ∃ (_raw_rawPush_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (rPush.β (le_refl E)) (Iso.refl (rPush.Φ E))),
  ∃ (_raw_rawPush_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) U),
    HEq ((rPush.β a).hom.app ((pbcAmbientCompleteLocalization l Ω U E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω V a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K) ≫
        (pbcAmbientCompleteLocalization l Ω V M).map ((pPush a).hom.app K) ≫
        (FiniteStageRationalExchange.rawPush l Ω M q).map
          ((pbcAmbientCompleteIntegralComparison l Ω U a).inv.app K))),
  ∃ (_raw_rawPull_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    rPull.Φ E = FiniteStageRationalExchange.rawPull l Ω E q),
  ∃ (_raw_rawPull_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (rPull.Φ E).Additive),
  ∃ (_raw_rawPull_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (rPull.β (le_refl E)) (Iso.refl (rPull.Φ E))),
  ∃ (_raw_rawPull_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) V),
    HEq ((rPull.β a).hom.app ((pbcAmbientCompleteLocalization l Ω V E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω U a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K) ≫
        (pbcAmbientCompleteLocalization l Ω U M).map ((pPull a).hom.app K) ≫
        (FiniteStageRationalExchange.rawPull l Ω M q).map
          ((pbcAmbientCompleteIntegralComparison l Ω V a).inv.app K))),
  ∃ (kar_karPush : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω U)
    (pbcAmbientCompleteSystem l Ω V)),
  ∃ (_kar_karPush_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    kar_karPush.Φ E = (functorExtension₂ _ _).obj (rPush.Φ E)),
  ∃ (_kar_karPush_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (kar_karPush.Φ E).Additive),
  ∃ (_kar_karPush_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (kar_karPush.β a) ((functorExtension₂ _ _).mapIso (rPush.β a))),
  ∃ (_kar_karPush_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (kar_karPush.β (le_refl E)) (Iso.refl (kar_karPush.Φ E))),
  ∃ (kar_karPull : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω V)
    (pbcAmbientCompleteSystem l Ω U)),
  ∃ (_kar_karPull_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    kar_karPull.Φ E = (functorExtension₂ _ _).obj (rPull.Φ E)),
  ∃ (_kar_karPull_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (kar_karPull.Φ E).Additive),
  ∃ (_kar_karPull_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (kar_karPull.β a) ((functorExtension₂ _ _).mapIso (rPull.β a))),
  ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (kar_karPull.β (le_refl E)) (Iso.refl (kar_karPull.Φ E))

end Operations

section Square

variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x))]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
  [iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
  (sq : ChosenCartesianSquare h e f g)

/-- The complete finite-stage rational and Karoubi exchange coherence conclusion.
Prefixes cf, cg, ch, ce refer respectively to f, g, h, e. The operation predicate
is asserted for each of the four morphisms before specifying the composite comparisons.
Source: sketch32, lines 1191--1228, 1262--1279 and 1291--1321
(blueprint: lem-sbc-finite-stage-rational-exchange-coherence). -/
def HasCoherence : Prop :=
  ∃ (cf_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) f ⋙
        pbcAmbientCompleteIntegralTransition l Ω S a ≅
      pbcAmbientCompleteIntegralTransition l Ω X a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) f),
  ∃ (cf_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) f ⋙
        pbcAmbientCompleteIntegralTransition l Ω X a ≅
      pbcAmbientCompleteIntegralTransition l Ω S a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) f),
  ∃ (cf_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω X)
    (pbcAmbientCompleteRawSystem l Ω S)),
  ∃ (cf_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω S)
    (pbcAmbientCompleteRawSystem l Ω X)),
  ∃ (cg_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) g ⋙
        pbcAmbientCompleteIntegralTransition l Ω S a ≅
      pbcAmbientCompleteIntegralTransition l Ω T a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) g),
  ∃ (cg_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) g ⋙
        pbcAmbientCompleteIntegralTransition l Ω T a ≅
      pbcAmbientCompleteIntegralTransition l Ω S a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) g),
  ∃ (cg_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω S)),
  ∃ (cg_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω S)
    (pbcAmbientCompleteRawSystem l Ω T)),
  ∃ (ch_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) h ⋙
        pbcAmbientCompleteIntegralTransition l Ω X a ≅
      pbcAmbientCompleteIntegralTransition l Ω Y a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) h),
  ∃ (ch_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) h ⋙
        pbcAmbientCompleteIntegralTransition l Ω Y a ≅
      pbcAmbientCompleteIntegralTransition l Ω X a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) h),
  ∃ (ch_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω Y)
    (pbcAmbientCompleteRawSystem l Ω X)),
  ∃ (ch_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω X)
    (pbcAmbientCompleteRawSystem l Ω Y)),
  ∃ (ce_pPush : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPush l (pbcFiniteField.{u} l Ω E) e ⋙
        pbcAmbientCompleteIntegralTransition l Ω T a ≅
      pbcAmbientCompleteIntegralTransition l Ω Y a ⋙
        sbcPush l (pbcFiniteField.{u} l Ω M) e),
  ∃ (ce_pPull : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcPull l (pbcFiniteField.{u} l Ω E) e ⋙
        pbcAmbientCompleteIntegralTransition l Ω Y a ≅
      pbcAmbientCompleteIntegralTransition l Ω T a ⋙
        sbcPull l (pbcFiniteField.{u} l Ω M) e),
  ∃ (ce_rPush : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω Y)
    (pbcAmbientCompleteRawSystem l Ω T)),
  ∃ (ce_rPull : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω Y)),
  HasOperationCoherence l Ω f cf_pPush cf_pPull cf_rPush cf_rPull ∧
  HasOperationCoherence l Ω g cg_pPush cg_pPull cg_rPush cg_rPull ∧
  HasOperationCoherence l Ω h ch_pPush ch_pPull ch_rPush ch_rPull ∧
  HasOperationCoherence l Ω e ce_pPush ce_pPull ce_rPush ce_rPull ∧
  ∃ (rawF : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω X)),
  ∃ (rawG : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω T)
    (pbcAmbientCompleteRawSystem l Ω X)),
  ∃ (_rawF_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    rawF.Φ E = sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g)),
  ∃ (_rawG_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    rawG.Φ E = sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h)),
  ∃ (_rawF_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (rawF.Φ E).Additive),
  ∃ (_rawG_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (rawG.Φ E).Additive),
  ∃ (_rawF_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (rawF.β (le_refl E)) (Iso.refl (rawF.Φ E))),
  ∃ (_rawG_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (rawG.β (le_refl E)) (Iso.refl (rawG.Φ E))),
  ∃ (_rawF_composite : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : pbcAmbientCompleteStage l Ω T E),
    HEq ((rawF.β a).hom.app K)
      ((cf_rPull.β a).hom.app ((cg_rPush.Φ E).obj K) ≫
        (cf_rPull.Φ M).map ((cg_rPush.β a).hom.app K))),
  ∃ (_rawG_composite : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : pbcAmbientCompleteStage l Ω T E),
    HEq ((rawG.β a).hom.app K)
      ((ch_rPush.β a).hom.app ((ce_rPull.Φ E).obj K) ≫
        (ch_rPush.Φ M).map ((ce_rPull.β a).hom.app K))),
  ∃ (_rawF_normalization : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    HEq ((rawF.β a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf_pPull a).hom.app
              ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map
              ((cg_pPush a).hom.app K)) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M)
          (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).inv.app K))),
  ∃ (_rawG_normalization : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    HEq ((rawG.β a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K))
      ((pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch_pPush a).hom.app
              ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map
              ((ce_pPull a).hom.app K)) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M)
          (h := h) (e := e)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).inv.app K))),
  ∃ (rawAlpha : StageSystem.Morphism.Hom rawF rawG),
  ∃ (_rawAlpha_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω), HEq (rawAlpha.τ E)
    (sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq)),
  ∃ (karF : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T)
    (pbcAmbientCompleteSystem l Ω X)),
  ∃ (karG : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T)
    (pbcAmbientCompleteSystem l Ω X)),
  ∃ (_karF_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    karF.Φ E = (functorExtension₂ _ _).obj (rawF.Φ E)),
  ∃ (_karG_eq : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    karG.Φ E = (functorExtension₂ _ _).obj (rawG.Φ E)),
  ∃ (_karF_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (karF.Φ E).Additive),
  ∃ (_karG_additive : ∀ (E : Padic.FiniteCoefficientFields l Ω), (karG.Φ E).Additive),
  ∃ (_karF_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (karF.β a) ((functorExtension₂ _ _).mapIso (rawF.β a))),
  ∃ (_karG_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (karG.β a) ((functorExtension₂ _ _).mapIso (rawG.β a))),
  ∃ (_karF_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (karF.β (le_refl E)) (Iso.refl (karF.Φ E))),
  ∃ (_karG_unit : ∀ (E : Padic.FiniteCoefficientFields l Ω),
    HEq (karG.β (le_refl E)) (Iso.refl (karG.Φ E))),
  ∃ (karAlpha : StageSystem.Morphism.Hom karF karG),
  ∀ (E : Padic.FiniteCoefficientFields l Ω), HEq (karAlpha.τ E)
    ((functorExtension₂ _ _).map (sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq))

end Square

end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
