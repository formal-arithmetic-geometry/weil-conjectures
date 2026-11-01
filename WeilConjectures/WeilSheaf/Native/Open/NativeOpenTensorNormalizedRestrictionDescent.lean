/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
public import WeilConjectures.SixFunctors.NativeNormalizedRestrictionProof.NativeOpenTensorNativeTotalStage3
public import WeilConjectures.WeilSheaf.NativeOpenTensorNativeNormalizedComparisonStage3
public import WeilConjectures.WeilSheaf.NativeOpenTensorNativePairRestrictionStage3
public import WeilConjectures.WeilSheaf.NativeOpenTensorNativeSheafStage3

/-! # Normalized native open tensor restriction descent

Source: Stacks 0GL1, 06YN and 012Z; native open tensor proof steps 3--6.
(blueprint: lem-sf-native-open-tensor-restriction-descent)
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

/-- Totalize the balanced restriction comparison and descend it to the derived category.

Source: Stacks 0GL1, 06YN and 012Z.
(blueprint: lem-sf-native-open-tensor-restriction-descent)

The proof uses the native sheaf, total, pair-restriction and normalized comparison
stages. Their hypotheses retain the native model links, while this declaration only
packages the resulting fields and the heterogeneous sheaf-map equality. -/
theorem native_open_tensor_restriction_descent (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels cN)
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m) :
    Nonempty (NativeOpenTensorRestrictionDescentData k₀ l j s m) := by
  let stages : NativeRestrictionStageInputs k₀ l j s m := {
    restriction_kflat := s.restriction_kflat
    sheaf := nativeSheafComparisonStage3 k₀ l j s m hm
    total := fun sr => totalComparisonStage3 k₀ l j s m hm sr
    pair := nativePairRestrictionStage3 k₀ l j (U := U) (Z := Z) }
  exact normalizedComparisonStage3 k₀ l j s m hm stages

end AlgebraicGeometry.ProEtaleWeilSheaf
