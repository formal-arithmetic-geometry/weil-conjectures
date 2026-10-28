/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NativeOpenTensorComparisonData
import Sheaf.Paper.NativeOpenTensorRestrictionDescent
import Sheaf.Paper.NativeOpenTensorProjectionDescent

/-! # Native open tensor derived comparisons

Source: Stacks 0GL1 and 06YN; native open tensor proof steps 3--6.
(blueprint: new-sf-native-open-tensor-comparisons)

The total-complex comparison and the restriction comparison are obtained by
localizing the corresponding chain maps.  This component records only their
existence; the normalization and presentation data are supplied separately.
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

-- Preserve the original names of the existential witnesses in the statement.
set_option linter.unusedVariables false in
/-- The native derived restriction and open tensor comparisons exist.

Source: Stacks 0GL1 and 06YN, localization of the chain comparisons in the
native open tensor proof.  The chain maps are totalized degreewise and then
localized on the two-sided K-flat resolving subcategories; the localization
universal property gives natural isomorphisms on all derived objects.
(blueprint: new-sf-native-open-tensor-comparisons)
-/
theorem native_open_tensor_comparisons (s : NativeOpenTensorData k₀ l j) :
    ∃ (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
        (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
      (gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j), True := by
  obtain ⟨rho⟩ := native_open_tensor_restriction_comparison k₀ l j s
  obtain ⟨gamma⟩ := native_open_tensor_projection_comparison k₀ l j s
  exact ⟨rho, gamma, trivial⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
