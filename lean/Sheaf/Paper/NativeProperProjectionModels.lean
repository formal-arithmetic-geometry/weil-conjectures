/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.NativeProperProjectionComparisons

/-! # Resolution models for native proper projection

Source: BS 6.8.14--6.8.15; Stacks 070I, 08BJ, 07A4 and 0G7E.
(blueprint: lem-sf-native-proper-projection-models).

These comparisons concern resolutions and tensor pullback; no projection-formula
isomorphism or invertibility assertion is included.
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
-- The representative and adjunction squares require more than 200000 heartbeats.
/-- Resolution and tensor comparison data before taking the projection mate.
Source: Steps 1--4 of lem-sf-native-proper-projection-realization;
BS 6.8.14--6.8.15 and Stacks 08BJ, 07A4, 0G7E
(blueprint: lem-sf-native-proper-projection-models). -/
structure NativeProperProjectionModels where
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

/-- The native and ordinary operations have compatible resolution models.
Source: Steps 1--4 of lem-sf-native-proper-projection-realization;
BS 6.8.14--6.8.15 and Stacks 070I, 08BJ, 07A4, 0G7E
(blueprint: lem-sf-native-proper-projection-models).

Proof: apply the proper-adjunction realization theorem to the geometric base
change of p and retain the source and target realization, finite normalization,
and Hom data of its family. The coefficient-ring comparison identifies both
coefficient maps with precomposition. Compose native forgetting with the section
presentation equivalences. The lifted sheaf adjunction and Frobenius mate give
pull and pushSheaf; on sections pushSheaf is the identity. Exact pullback and
exact forgetting preserve the required acyclicity. Equivariant K-injective
resolutions stay K-injective after forgetting; both pushforwards on such a
resolution are the same ordinary complex. The normalized fixed-pair derived
comparison gives push and pushRepresentative. Computing the derived counit on
that resolution gives counit, independently of the resolution.
For tensors use equivariant K-flat flat-term resolutions. On sheaves the balanced
map sends b tensor (x tensor y) to (b tensor x) tensor (1 tensor y); its inverse
multiplies coefficients. These maps commute with Frobenius. Totalize with the
signed differential and retain each coproduct insertion. Ringed pullback preserves
K-flatness, and conservative forgetting detects acyclicity. Localization of these
maps gives balanced, sourceTensor and targetTensor, including their generator
and representative equations. The same insertion formulas give pullTensor.
None of these constructions uses invertibility of a projection mate. Zero inputs,
empty schemes and identity maps use exactly the same resolution formulas. -/
theorem native_proper_projection_models [IsProper p] :
    Nonempty (NativeProperProjectionModels k₀ l p) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
