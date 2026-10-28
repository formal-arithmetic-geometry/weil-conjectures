/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.NativeProperProjectionComparisons

/-! # Ordinary proper projection formula

Source: BS 6.8.14--6.8.15; Stacks 070I, 08BJ, 07A4 and 0G7E.
(blueprint: lem-sf-ordinary-proper-projection-invertible).

The formula concerns ordinary continuous-coefficient modules, with no Weil structure.
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

/-- The ordinary counit projection mate is invertible on bounded constructible
continuous-coefficient complexes.
Source: Step 6 and the invertibility assertion of Step 7 of
lem-sf-native-proper-projection-realization; blueprint latest,
fix-lem-tensor-adjunction.proof.md Step 1, second Hom bijection;
BS 6.8.14--6.8.15
(blueprint: lem-sf-ordinary-proper-projection-invertible).

Proof: by the exact essential-image clause of the locally finite realization,
lift the two bounded constructible complexes to the common-stage category.
The section-derived presentation carries the lifting isomorphisms to the ordinary
module category. Each common-stage object has a finite coefficient-field model;
take the compositum so both objects have models over the same field. Over this
field bounded constructibility is the finite-Tor domain. Apply the rational
projection formula to integral representatives and extend to their finite cones,
shifts and rationalized arrows, then pass to their common-stage classes.
Use the compactification (identity,p). The identity extension by zero and its
tensor comparison are identity maps under the unit comparison, so its projection
arrow is exactly the counit mate properCommonProjection. It is therefore invertible.
The tensor, unit and counit equations in the supplied proper comparison identify
the ordinary image of this arrow with properOrdinaryProjection, conjugated by
the specified tensor, pull and push isomorphisms. The ordinary realization
preserves its inverse. Naturality of the counit mate transports invertibility
along the two lifting isomorphisms to the original complexes. This uses finite
Tor amplitude only over a field; it imposes no additional hypothesis on either
bounded constructible complex. The same argument includes zero objects and
empty schemes; no faithful forgetting of derived Weil morphisms is used. -/
theorem properOrdinaryProjection_isIso [IsProper p]
    (R : LocallyFiniteAdicRealization.Realization l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (S : LocallyFiniteAdicRealization.Realization l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
    [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
    (A : At l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R)
    (B : At l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S)
    (hl : IsUnit (l : AlgebraicClosure k₀))
    (C : Proper.Comparison l (NativeBaseChange.geometricMap k₀ p) R S
      (AlgebraicClosure k₀) hl A B)
    (M : DerivedCategory (modules l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R))
    (N : DerivedCategory (modules l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S))
    (hM : boundedConstructible l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R M)
    (hN : boundedConstructible l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S N) :
    IsIso (properOrdinaryProjection k₀ l p R S A B C.operations C.tensor M N) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
