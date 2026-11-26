/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorPresentationExistence

/-! # Localizing the native open tensor comparison

The sheaf-level open tensor comparisons are totalized and localized to the unbounded native
derived categories.

## Implementation details

The fixed sheaf comparison and its inverse are applied in every bidegree; the signed
differential `dx ⊗ y + (-1)^p x ⊗ dy` makes these natural chain isomorphisms. Extension by
zero and restriction preserve flat terms and K-flatness, hence the resolving subcategories of
flat-term equivariant K-flat resolutions on the twisted action site, so the chain comparisons
localize; the native K-flat tensor models give the two representative normalization squares of
`OpenTensorPresentation`.

## References

* Stacks Project, Tags 0GL1 and 06YN.
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

-- The dependent presentation fields require a larger elaboration budget.
/-- The fixed sheaf comparisons, totalized and descended to the unbounded ambient derived
categories, give derived comparisons `rho` and `gamma` and an open tensor presentation whose
fields are the native functors, K-flat predicates, models and insertions. -/
theorem native_open_tensor_localization (s : NativeOpenTensorData k₀ l j) :
    ∃ (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
        (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
      (gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z)),
      HEq c.E (extensionByZero k₀ l j) ∧ HEq c.R (upperStar k₀ l j) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧
      HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧
      HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafGamma s.sheafGamma ∧ HEq c.gamma gamma ∧
      HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction rho := by
  exact native_open_tensor_presentation_exists k₀ l j s

end AlgebraicGeometry.ProEtaleWeilSheaf
