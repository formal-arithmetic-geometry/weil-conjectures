/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.NativeOpenTensorComparisonData

/-! # Forgetting normalization for the native open tensor

Source: Stacks 0GL1 and 0E8I, native open tensor proof step 8
(blueprint: new-lem-sf-native-open-tensor-forget-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The native derived open tensor presentation admits the prescribed ordinary
forgetting comparison data.

Source: Stacks 0GL1, 0E8I and 015F; forgetting the normalized representative
squares through the exact open functors identifies them with the ordinary
unit-normalized squares. The proof uses the fixed tensor comparisons, the
ordinary open tensor theorem, and the Frobenius resolution theorem.
(blueprint: new-lem-sf-native-open-tensor-forget-normalization). -/
theorem native_open_tensor_forget_normalization (s : NativeOpenTensorData k₀ l j)
    (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
      (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
    (gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (_hc :
      HEq c.E (extensionByZero k₀ l j) ∧ HEq c.R (upperStar k₀ l j) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafGamma s.sheafGamma ∧ HEq c.gamma gamma ∧
      HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction rho) :
    Nonempty (OpenTensorForgetData
    (nativeOpenExtension k₀ l j) (nativeOpenPull k₀ l j)
    (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory
    (nativeForget k₀ l U) (nativeForget k₀ l Z)
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z)
    (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor
    (nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor
    (nativeOpenForgetExtension k₀ l j) (nativeOpenForgetPull k₀ l j)
    (nativeDerivedClosedComparison k₀ l U).tensorComparison
    (nativeDerivedClosedComparison k₀ l Z).tensorComparison
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapExactDerivedCategory
      rho gamma) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
