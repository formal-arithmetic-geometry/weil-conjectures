/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.Paper.NativeProperProjectionComparisons

/-! # Native section adjunction on common resolution models

Source: Stacks 070I, 08BJ; native proper-projection model proof, steps 2--3.
The statement compares only inverse and direct image, without tensor data.
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

variable
  (R : LocallyFiniteAdicRealization.Realization l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (S : LocallyFiniteAdicRealization.Realization l
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
  [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
  (O : Proper.Operations l (NativeBaseChange.geometricMap k₀ p) R S)

/-- The inverse/direct-image part of the normalized section comparison.
Source: Stacks 070I, 08BJ and native proper-projection model proof, steps 2--3
(blueprint: lem-sf-native-proper-section-adjunction-models). -/
structure NativeProperSectionAdjunctionModels where
  pull : nativeOpenPull k₀ l p ⋙ properSectionDerived k₀ l Z R ≅
    properSectionDerived k₀ l Y S ⋙
      ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) O.coefficient
  pushSheaf : lowerStar k₀ l p ⋙ properSectionForget k₀ l Y S ≅
    properSectionForget k₀ l Z R ⋙
      ContinuousRational.DirectImage.modulePush
        (NativeBaseChange.geometricMap k₀ p) O.coefficient
  pushSections : ∀ M V x, HEq ((pushSheaf.hom.app M).val.app V x) x
  push : (lowerStar k₀ l p).rightDerivedFunctor ⋙ properSectionDerived k₀ l Y S ≅
    properSectionDerived k₀ l Z R ⋙
      ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) O.coefficient
  pushRepresentative : ∀ (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
      (_hI : I.IsKInjective),
    (properSectionDerived k₀ l Y S).map (properNativePushUnit k₀ l p I) ≫
      push.hom.app (DerivedCategory.Q.obj I) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          ((properSectionFactors k₀ l Z R).hom.app I) =
    (properSectionFactors k₀ l Y S).hom.app
        (((lowerStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((properPushSheafCochain k₀ l p R S O pushSheaf).hom.app I) ≫
      ContinuousRational.DirectImage.pushUnit (NativeBaseChange.geometricMap k₀ p)
        O.coefficient
        ((properSectionCochain k₀ l Z R).obj I)
  counit : ∀ A,
    (properSectionDerived k₀ l Z R).map
        ((derivedUpperStarLowerStarAdjunction k₀ l p).counit.app A) =
      pull.hom.app ((lowerStar k₀ l p).rightDerivedFunctor.obj A) ≫
        (ContinuousRational.derivedPull
          (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          (push.hom.app A) ≫
        O.adjunction.counit.app
          ((properSectionDerived k₀ l Z R).obj A)

/-- The actual sheaf and derived adjunctions agree in section coordinates.
Source: Stacks 070I, 08BJ; BS 6.8.14--6.8.15; native proper-projection model proof,
steps 2--3 (blueprint: lem-sf-native-proper-section-adjunction-models).

Proof: O.functions identifies its coefficient map with precomposition. Thus the
underlying native direct image and ordinary module direct image have the same
sections and action. Their identity comparison is pushSheaf. Taking its left
adjoint mate gives the sheaf inverse-image comparison, with the actual counit
square; the fixed-pair adjunction lift retains these carrier maps. Native inverse
image is exact, as is the section presentation. Localize this sheaf comparison
termwise to obtain pull. On an equivariant K-injective I, forgetting preserves
K-injectivity by the exact integer-orbit left adjoint; the section equivalence
also preserves it. Both direct images are therefore computed by the same complex.
The universal normalized right-derived comparison supplies push, and its unit
identity on I is exactly pushRepresentative, including the two properSectionFactors
and the termwise pushSheaf map. This comparison is independent of the chosen
resolution by the bijection on maps into K-injectives. On these same models the
native and ordinary derived counits are the localized sheaf counits followed by
the inverse target augmentation. O.transpose fixes the ordinary derived adjunction
on these representatives, so the sheaf counit square gives counit. All maps are
natural on chain maps and homotopies and hence on the localization. No tensor
comparison or projection formula is used. The construction also applies to zero
complexes, empty schemes and identity maps. -/
theorem native_proper_section_adjunction_models
    (hR : (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence)
    (hS : (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S).IsEquivalence) :
    Nonempty (NativeProperSectionAdjunctionModels k₀ l p R S O) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
