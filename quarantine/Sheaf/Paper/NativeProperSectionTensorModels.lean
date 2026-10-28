/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.Paper.NativeProperSectionAdjunctionModels

/-! # Tensor comparison for normalized native section adjunctions

Source: Stacks 07A4, 0G7E; native proper-projection model proof, step 4.
No realization data or direct-image comparison is constructed by this lemma.
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

variable
  (A : At l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R)
  (B : At l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S)
  (C : Proper.TensorComparison l (NativeBaseChange.geometricMap k₀ p) R S O A B)
  (J : NativeProperSectionAdjunctionModels k₀ l p R S O)

/-- The tensor part of the native proper-projection resolution calculation.
Source: Stacks 07A4, 0G7E and BS 6.8.14--6.8.15; native proper-projection model
proof, step 4 (blueprint: lem-sf-native-proper-section-tensor-models).

Proof: construct the section tensor comparison on sheaves from the identity on
underlying balanced tensors. For complexes, take the direct sum of these maps on
all (i,j) summands. Its generator formula is precisely ProperSectionTensor.generators;
both differentials are d tensor 1 plus (-1)^i 1 tensor d. The inverse is obtained
by the same underlying tensor universal property. The exact section equivalence
and the exact orbit-induction adjunction transfer both quasi-isomorphism tests for
K-flatness. Forgetting native K-flat complexes is K-flat: test against an ordinary
acyclic complex Q by its exact orbit induction, whose underlying complex is the
direct sum of all Frobenius translates of Q. The ordinary tensor with Q is the
split degree-zero summand of the forgotten acyclic total tensor. Thus it too is
acyclic. Apply the same argument in the other tensor variable. Tensor descent
therefore gives TZ and TY, with the stated representative equation on every
K-flat pair, by uniqueness of the tensor-Hom adjunction comparisons.

For p, use the balanced sheaf maps b tensor (x tensor y) maps to
(b tensor x) tensor (1 tensor y), and the inverse multiplies coefficients.
They commute with Frobenius by the coefficient precomposition equation. Their
termwise totalizations retain each summand insertion. Ordinary inverse image
preserves flat-term K-flat models; exact conservative forgetting gives the native
K-flat tests. Localization constructs balanced with its presentation, compatibility,
sheaf_forget and representative normalizations. Compute the square on simultaneous
K-flat resolutions. C.representative and TZ.representative and TY.representative
identify its four sides with these same balanced sheaf maps; no extra signs appear.
The pull in J is the canonical one: pushSections and pushRepresentative fix its
right comparison on K-injectives, and J.counit fixes its left adjoint mate. Thus it
is this localized sheaf pull comparison. The two insertion formulas agree on every
pure tensor, proving the square; localization and naturality give it for arbitrary
M and N. Empty sites, zero inputs and identity p use the same formulas. -/
theorem native_proper_section_tensor_models
    (hR : (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence)
    (hS : (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S).IsEquivalence) :
    ∃ (TZ : ProperSectionTensor k₀ l Z R A) (TY : ProperSectionTensor k₀ l Y S B)
      (balanced : NativeProjectionTensorComparison k₀ l p),
    ∀ M N,
    (properSectionDerived k₀ l Z R).map (balanced.mu.hom.app (M, N)) ≫
      TZ.tensor.hom.app
        ((nativeOpenPull k₀ l p).obj M, (nativeOpenPull k₀ l p).obj N) ≫
      A.closed.tensor.map (Prod.mkHom (J.pull.hom.app M) (J.pull.hom.app N)) =
    J.pull.hom.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      (ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          (TY.tensor.hom.app (M, N)) ≫
      C.tensor.hom.app
        ((properSectionDerived k₀ l Y S).obj M,
          (properSectionDerived k₀ l Y S).obj N) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
