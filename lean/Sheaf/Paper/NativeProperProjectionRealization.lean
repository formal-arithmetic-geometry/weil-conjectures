/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.NativeCompactProjectionFormula
public import Sheaf.Paper.NativeProperProjectionComparisons
public import Sheaf.Paper.AdicProperAdjunctionRealization
public import Sheaf.Paper.DerivedWeilTensorOperations
public import Sheaf.Paper.NativeWeilClosedForgetful
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Localization
public import Sheaf.Paper.AdicQbarConstructibleRealization

import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.NativeDerivedWeilTensorConstructible
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import Sheaf.CategoryTheory.FixedPairDerivedForgetComparison
import Sheaf.Paper.LocallyFiniteCoefficientRingRealization
import WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate
import Sheaf.WeilSheaf.NativePullbackStarPreservation
import Sheaf.Algebra.Homology.RingedForgetTensorTransposition
import Sheaf.Paper.WeilFrobeniusActionResolutions
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Realization of the native proper projection morphism

Source: latest blueprint, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection; Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15, pp. 61--62
(blueprint: lem-sf-native-proper-projection-realization).

The arrow is the actual ambient derived counit mate. Its comparisons retain their
sheaf generators, K-flat totalizations and equivariant K-injective computation.

## Main definitions

* `NativeProperProjectionRealization`: the proper projection and its compatibility squares.

## Main statements

* `native_proper_projection_realization`: existence of the normalized natural isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  AlgebraicGeometry.Scheme.ContinuousRational.modulePull
  AlgebraicGeometry.Scheme.ContinuousRational.derivedPull

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures Opposite
open WeilConjectures.AdicQbarRealization
open AlgebraicGeometry.Scheme
open scoped TensorProduct AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

set_option maxHeartbeats 800000 in
-- Elaborating the representative and adjunction squares requires more than 200000 heartbeats.
/-- All normalized comparisons for the native proper projection. These are output
data, not hypotheses on the morphism or on its constructible derived inputs.
Source: BS 6.8.14--6.8.15; native projection proof Steps 1--8
(blueprint: lem-sf-native-proper-projection-realization). -/
structure NativeProperProjectionRealization where
  source : LocallyFiniteAdicRealization.Realization l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
  target : LocallyFiniteAdicRealization.Realization l
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
  [sourceUnits : ∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
  [targetUnits : ∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
  sourceAt : At l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source
  targetAt : At l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target
  sourcePresentation :
    (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source).IsEquivalence
  targetPresentation :
    (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target).IsEquivalence
  sourceFinite : ∀ E,
    FiniteNormalization l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source sourceAt E
  targetFinite : ∀ E,
    FiniteNormalization l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target targetAt E
  sourceHom : HomLaws l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source sourceAt
  targetHom : HomLaws l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target targetAt
  primeUnit : IsUnit (l : AlgebraicClosure k₀)
  comparison : Proper.Comparison l (NativeBaseChange.geometricMap k₀ p) source target
    (AlgebraicClosure k₀) primeUnit sourceAt targetAt
  sourceTensor : ProperSectionTensor k₀ l Z source sourceAt
  targetTensor : ProperSectionTensor k₀ l Y target targetAt
  balanced : NativeProjectionTensorComparison k₀ l p
  pull : nativeOpenPull k₀ l p ⋙ properSectionDerived k₀ l Z source ≅
    properSectionDerived k₀ l Y target ⋙
      ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient
  pushSheaf : lowerStar k₀ l p ⋙ properSectionForget k₀ l Y target ≅
    properSectionForget k₀ l Z source ⋙
      ContinuousRational.DirectImage.modulePush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient
  pushSections : ∀ M V x, HEq ((pushSheaf.hom.app M).val.app V x) x
  push : (lowerStar k₀ l p).rightDerivedFunctor ⋙ properSectionDerived k₀ l Y target ≅
    properSectionDerived k₀ l Z source ⋙
      ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient
  injective : ∀ I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      ((properSectionCochain k₀ l Z source).obj I)
  pushRepresentative : ∀ (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
      (_hI : I.IsKInjective),
    (properSectionDerived k₀ l Y target).map (properNativePushUnit k₀ l p I) ≫
      push.hom.app (DerivedCategory.Q.obj I) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
          ((properSectionFactors k₀ l Z source).hom.app I) =
    (properSectionFactors k₀ l Y target).hom.app
        (((lowerStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((properPushSheafCochain k₀ l p source target comparison.operations pushSheaf).hom.app I) ≫
      ContinuousRational.DirectImage.pushUnit (NativeBaseChange.geometricMap k₀ p)
        comparison.operations.coefficient
        ((properSectionCochain k₀ l Z source).obj I)
  counit : ∀ A,
    (properSectionDerived k₀ l Z source).map
        ((derivedUpperStarLowerStarAdjunction k₀ l p).counit.app A) =
      pull.hom.app ((lowerStar k₀ l p).rightDerivedFunctor.obj A) ≫
        (ContinuousRational.derivedPull
          (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
          (push.hom.app A) ≫
        comparison.operations.adjunction.counit.app
          ((properSectionDerived k₀ l Z source).obj A)
  pullTensor : ∀ M N,
    (properSectionDerived k₀ l Z source).map (balanced.mu.hom.app (M, N)) ≫
      sourceTensor.tensor.hom.app
        ((nativeOpenPull k₀ l p).obj M, (nativeOpenPull k₀ l p).obj N) ≫
      sourceAt.closed.tensor.map (Prod.mkHom (pull.hom.app M) (pull.hom.app N)) =
    pull.hom.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      (ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
          (targetTensor.tensor.hom.app (M, N)) ≫
      comparison.tensor.tensor.hom.app
        ((properSectionDerived k₀ l Y target).obj M,
          (properSectionDerived k₀ l Y target).obj N)
  projection : properNativeProjectionSource k₀ l p ≅ properNativeProjectionTarget k₀ l p
  projectionMate : ∀ (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y),
    projection.hom.app (A, T) = nativeProjectionProperMate k₀ l p balanced A.obj T.obj
  projectionForget : ∀ (A : WeilComplex k₀ l Z) (T : WeilComplex k₀ l Y),
    (properSectionDerived k₀ l Y target).map
        (nativeProjectionProperMate k₀ l p balanced A.obj T.obj) ≫
      push.hom.app ((nativeDerivedTensor k₀ l Z).obj
        (A.obj, (nativeOpenPull k₀ l p).obj T.obj)) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
        (sourceTensor.tensor.hom.app (A.obj, (nativeOpenPull k₀ l p).obj T.obj) ≫
          sourceAt.closed.tensor.map (Prod.mkHom (𝟙 _) (pull.hom.app T.obj))) =
    targetTensor.tensor.hom.app
        ((lowerStar k₀ l p).rightDerivedFunctor.obj A.obj, T.obj) ≫
      targetAt.closed.tensor.map (Prod.mkHom (push.hom.app A.obj) (𝟙 _)) ≫
      properOrdinaryProjection k₀ l p source target sourceAt targetAt
        comparison.operations comparison.tensor
        ((properSectionDerived k₀ l Z source).obj A.obj)
        ((properSectionDerived k₀ l Y target).obj T.obj)
  projectionRealization : ∀
      (K : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    (ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target).map
        (properCommonProjection k₀ l p primeUnit K L) ≫
      comparison.b.hom.app
        ((commonStageDerivedTensor l (PadicAlgCl l)
          (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
          (K, (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj L)) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
        (sourceAt.tensor.inv.app (K,
          (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj L) ≫
          sourceAt.closed.tensor.map (Prod.mkHom (𝟙 _) (comparison.a.hom.app L))) =
    targetAt.tensor.inv.app ((properCommonPush k₀ l p primeUnit).obj K, L) ≫
      targetAt.closed.tensor.map (Prod.mkHom (comparison.b.hom.app K) (𝟙 _)) ≫
      properOrdinaryProjection k₀ l p source target sourceAt targetAt
        comparison.operations comparison.tensor
        ((ordinary l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source).obj K)
        ((ordinary l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target).obj L)

/-- The native proper projection is a natural isomorphism on arbitrary bounded
constructible derived inputs, and its actual counit mate has the stated ordinary
and common-stage realizations, with the proper identity-open normalization.
Source: latest blueprint, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection; Bhatt--Scholze 6.8.14--6.8.15, pp. 61--62
(blueprint: lem-sf-native-proper-projection-realization).

Proof:
1. The coefficient-ring comparison of lem-sf-locally-finite-coefficient-ring-realization
identifies locally finite spans and locally finite extension values: a finite basis
lies in one finite subextension. Its coefficient-map square identifies precomposition.
The native closed-forgetful theorem and the constructible realization equivalence
supply common-stage lifts of the underlying A and T. Properness and separated finite
type are preserved by geometric base change.
2. Lift the actual sheaf inverse/direct-image adjunction using
lem-sf-fixed-pair-adjunction-lift and the native Frobenius mate relation. Exact and
conservative forgetting detects exact pullback. Equivariant K-flat and K-injective
resolutions are supplied by lem-sf-weil-frobenius-action-resolutions.
3. On A to I with I equivariant K-injective, forgetting computes both pushforwards
on the same complex. Exact pullback implies pushforward preserves K-injectives by
termwise homotopy adjunction; maps into these complexes compute derived Hom by
lem-weil-pbc-kinjective-hom-derived. Thus the actual derived counit is the localized
sheaf counit followed by the inverse augmentation, on both sides. This gives
pushRepresentative and counit, using lem-sf-fixed-pair-derived-forget-comparison.
4. Balanced tensor maps send b tensor (x tensor y) to (b tensor x) tensor (1 tensor y)
and inversely multiply the two coefficients. They commute with Frobenius. Totalize
with differential d tensor 1 plus (-1)^i 1 tensor d on equivariant K-flat flat-term
resolutions. The ringed pullback K-flat theorem and conservative forgetting allow
derived descent. This gives balanced, the section tensor generators and models,
and pullTensor; use lem-sf-ringed-forget-tensor-transposition.
5. Form the actual native counit mate. The preceding counit and tensor squares
identify its forgotten composite with the ordinary projection mate of
lem-weil-pbc-ringed-projection-mate-exact. This gives projectionForget by functoriality;
faithfulness of derived forgetting is not assumed.
6. Descend A and T to a common finite coefficient field. At field stages bounded
constructible equals bounded constructible finite-Tor, so thm-sf-pf-field applies
to every T in the statement. Use compactification (identity,p) in def-exchange-projection:
the identity-open tensor comparison is the identity, leaving properCommonProjection.
7. Substitute the normalized proper-realization counit, unit and tensor equations
of lem-sf-adic-proper-adjunction-realization in that common-stage mate. This gives
projectionRealization with its actual a and b, not merely an object isomorphism.
Since realization carries the field projection isomorphism to the ordinary mate,
the latter is invertible.
8. Conservative native forgetting detects invertibility. The inverse is natural
by multiplying the naturality square by the two inverses. Native tensor closure
and pullback/direct-image preservation place source and target in the bounded
constructible full categories. Their full inclusions restrict the same arrow and
inverse. No restriction to lisse sheaves or single-degree derived objects is used.
-/
theorem native_proper_projection_realization [IsProper p] :
    Nonempty (NativeProperProjectionRealization k₀ l p) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
