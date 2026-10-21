/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.Paper.PbcDescentFunctors
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Sheaf.CategoryTheory.RingedSliceExtensionTensor
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.Paper.PbcScalarExtension

public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.Paper.CompleteCompactSupportProetale

/-! # Normalized coefficient-family data

Source: blueprint main-20261015, `sk-thm-sf-pf-field/thm-cbc-qbar.proof.md`,
opening scalar-extension paragraph; Stacks Tag 0E8I for the open tensor factor
(blueprint: def-cbc-normalized-coefficient-families).

## Main definitions

* `cbcScalarCompactSupportInverse`: the actual open/proper scalar mate composite.
* `CbcCompactSupportCoefficientFamily`: compact-support families with their
  integral, shift and scalar normalization.
* `CbcCompletedPullCoefficientFamily`: completed pullback families with their
  ordinary-balancing and completion-unit normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] cbcDerivedOpenAdjunction

/-- The inverse compact-support coefficient comparison, consisting of the inverse
open-unit mate followed by the inverse proper counit-tensor comparison.
Source: blueprint main-20261015, thm-cbc-qbar, opening coefficient paragraph;
Stacks Tag 0E8I for the open tensor factor
(blueprint: def-cbc-normalized-coefficient-families). -/
@[irreducible] def cbcScalarCompactSupportInverse (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    ((pbcIntegralDatum l F).push c.g).obj
        ((cbcDerivedOpenShriek (pbcIntegralDatum l F) c.i c.isOpenImmersion).obj
          ((pbcEmbeddingAmbientTensor l E F i X).obj K)) ⟶
      (pbcEmbeddingAmbientTensor l E F i Y).obj
        (((pbcIntegralDatum l E).push c.g).obj
          ((cbcDerivedOpenShriek (pbcIntegralDatum l E) c.i c.isOpenImmersion).obj K)) :=
  letI := c.isOpenImmersion
  ((pbcIntegralDatum l F).push c.g).map
      ((((mateEquiv (cbcDerivedOpenAdjunction (pbcIntegralDatum l E) c.i)
        (cbcDerivedOpenAdjunction (pbcIntegralDatum l F) c.i)).symm
          (TwoSquare.mk _ _ _ _
            (Functor.isoWhiskerLeft _
                (cbcDatumOrdinaryTransport (pbcIntegralDatum l F) c.i).symm ≪≫
              pbcScalarOrdinaryPullIso l E F i c.i ≪≫
              Functor.isoWhiskerRight
                (cbcDatumOrdinaryTransport (pbcIntegralDatum l E) c.i) _).inv)).natTrans).app K) ≫
    (pbcScalarDirectImageIso l E F i c.g).inv.app
      ((cbcDerivedOpenShriek (pbcIntegralDatum l E) c.i c.isOpenImmersion).obj K)

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The specified exact compact-support family on the raw rational stages.
The functors are fixed by integral localization, their shift maps by the actual
ambient shifts, and their inverse beta maps by the open/proper mate composite.
Source: blueprint main-20261015, thm-cbc-qbar, opening coefficient paragraph
(blueprint: def-cbc-normalized-coefficient-families). -/
structure CbcCompactSupportCoefficientFamily {f : X ⟶ Y} (c : Compactification f) where
  preserves : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
      (((pbcStageDatum.{u} l Ω E).push c.g).obj
        ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion).obj K.obj))
  family : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out) (pbcScalarSystem l Ω Y dY.out iY.out)
  localization : ∀ E : Padic.FiniteCoefficientFields l Ω,
    pbcStageLocalization l Ω X E ⋙ family.base.Φ E =
      pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g) (preserves E) ⋙
            pbcStageLocalization l Ω Y E
  shift : ∀ (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ)
    (K : pbcIntegralStage l Ω X E),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g).obj (K.obj⟦n⟧)))
      (ht : PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        (((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g).obj K.obj)⟦n⟧)),
      HEq ((@Functor.commShiftIso _ _ _ _ (family.base.Φ E) ℤ _ _ _
          (family.commShift E) n).hom.app
          ((pbcStageLocalization l Ω X E).obj K))
        ((pbcStageLocalization l Ω Y E).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩)
            ((((cbcOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion).mapDerivedCategory ⋙
              (pbcStageDatum.{u} l Ω E).push c.g).commShiftIso n).hom.app K.obj)))
  beta : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcIntegralStage l Ω X E),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω F)
        ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω F) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω F).push c.g).obj
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) X).obj K.obj)))
      (ht : PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω F)
        ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) Y).obj
            ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g).obj K.obj))),
      HEq
        ((eqToIso (localization F)).inv.app
            ((pbcIntegralScalarExtension l Ω X dX.out iX.out h).obj K) ≫
          (family.base.Φ F).map
            ((pbcScalarIntegralComparison l Ω X dX.out iX.out h).inv.app K) ≫
          (family.base.β h).inv.app ((pbcStageLocalization l Ω X E).obj K) ≫
          ((pbcScalarSystem l Ω Y dY.out iY.out).T h).map
            ((eqToIso (localization E)).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω Y dY.out iY.out h).hom.app
            ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
              (cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g) (preserves E)).obj K))
        ((pbcStageLocalization l Ω Y F).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩) (cbcScalarCompactSupportInverse l _ _
            (pbcFiniteFieldInclusion l Ω h) c K.obj)))
  unit : ∀ E : Padic.FiniteCoefficientFields l Ω,
    HEq (family.base.β (le_refl E)) (Iso.refl (family.base.Φ E))

/-- The actual completed pullback family, with its ordinary-balancing and
completion-unit normalized scalar comparison. Inverse beta is its localization.
Source: blueprint main-20261015, thm-cbc-qbar; scalar-extension proposition
(blueprint: def-cbc-normalized-coefficient-families). -/
structure CbcCompletedPullCoefficientFamily (g : Y ⟶ X) where
  preserves : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
    PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
      (((pbcStageDatum.{u} l Ω E).completedPull g).obj K.obj)
  family : StageSystem.CoherentExactMorphism
    (pbcScalarSystem l Ω X dX.out iX.out) (pbcScalarSystem l Ω Y dY.out iY.out)
  localization : ∀ E : Padic.FiniteCoefficientFields l Ω,
    pbcStageLocalization l Ω X E ⋙ family.base.Φ E =
      pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        ((pbcStageDatum.{u} l Ω E).completedPull g) (preserves E) ⋙
          pbcStageLocalization l Ω Y E
  comparison : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
    pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) X ⋙ (pbcStageDatum.{u} l Ω F).completedPull g ⟶
      (pbcStageDatum.{u} l Ω E).completedPull g ⋙
        pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
          (pbcFiniteFieldInclusion l Ω h) Y
  completionUnit : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcAmbientStage l Ω X E),
    (pbcStageDatum.{u} l Ω F).ordinaryToCompleted g
        ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) X).obj K) ≫
        (comparison h).app K =
      (Functor.isoWhiskerLeft _
          (cbcDatumOrdinaryTransport (pbcStageDatum.{u} l Ω F) g).symm ≪≫
        pbcScalarOrdinaryPullIso l _ _ (pbcFiniteFieldInclusion l Ω h) g ≪≫
        Functor.isoWhiskerRight
          (cbcDatumOrdinaryTransport (pbcStageDatum.{u} l Ω E) g) _).hom.app K ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) Y).map
            ((pbcStageDatum.{u} l Ω E).ordinaryToCompleted g K)
  beta : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcIntegralStage l Ω X E),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω F)
        (((pbcStageDatum.{u} l Ω F).completedPull g).obj
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) X).obj K.obj)))
      (ht : PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω F)
        ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) Y).obj
            (((pbcStageDatum.{u} l Ω E).completedPull g).obj K.obj))),
      HEq
        ((eqToIso (localization F)).inv.app
            ((pbcIntegralScalarExtension l Ω X dX.out iX.out h).obj K) ≫
          (family.base.Φ F).map
            ((pbcScalarIntegralComparison l Ω X dX.out iX.out h).inv.app K) ≫
          (family.base.β h).inv.app ((pbcStageLocalization l Ω X E).obj K) ≫
          ((pbcScalarSystem l Ω Y dY.out iY.out).T h).map
            ((eqToIso (localization E)).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω Y dY.out iY.out h).hom.app
            ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
              ((pbcStageDatum.{u} l Ω E).completedPull g) (preserves E)).obj K))
        ((pbcStageLocalization l Ω Y F).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩) ((comparison h).app K.obj)))
  unit : ∀ E : Padic.FiniteCoefficientFields l Ω,
    HEq (family.base.β (le_refl E)) (Iso.refl (family.base.Φ E))

end AlgebraicGeometry.Scheme
