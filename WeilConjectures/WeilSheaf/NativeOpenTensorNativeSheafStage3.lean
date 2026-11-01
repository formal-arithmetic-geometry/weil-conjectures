/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
import all WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorSheafComparisons

/-! Native balanced sheaf restriction comparison.
(blueprint: new-sf-native-open-tensor-sheaf-stage3)

Source: Stacks 0GL1 and 07A4; the native sheaf comparison is the
restriction map on the native open tensor sheaf. -/
@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u
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
structure SheafDataCore (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j)) where
  sr : nativeOpenSheafTensor k₀ l Z ⋙ upperStar k₀ l j ≅
    (upperStar k₀ l j).prod (upperStar k₀ l j) ⋙ nativeOpenSheafTensor k₀ l U
  hs : HEq m.sheafRestriction (fun M N ↦ sr.app (M, N))
@[irreducible] def SheafData (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j)) : Type _ :=
  SheafDataCore k₀ l j s m

def sheafData_sr (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (d : SheafData k₀ l j s m) : nativeOpenSheafTensor k₀ l Z ⋙ upperStar k₀ l j ≅
      (upperStar k₀ l j).prod (upperStar k₀ l j) ⋙ nativeOpenSheafTensor k₀ l U := by
  unfold SheafData at d
  exact d.sr

theorem sheafData_hs (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (d : SheafData k₀ l j s m) : HEq m.sheafRestriction
      (fun M N ↦ (sheafData_sr k₀ l j s m d).app (M, N)) := by
  unfold SheafData at d; exact d.hs

/-- The native balanced sheaf restriction isomorphism realizes the sheaf map of m.

Source: Stacks 07A4. (blueprint: new-sf-native-open-tensor-sheaf-stage3)

Proof: take for sr the natural isomorphism of native_open_tensor_sheaf_comparisons,
built by NatIso.ofComponents from s.sheafRestriction; its component at (M,N) is
s.sheafRestriction M N, and hm.sheafRestriction gives the HEq with m.sheafRestriction. -/
theorem nativeSheafComparisonStage3 (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m) :
    Nonempty (SheafData k₀ l j s m) := by sorry
end AlgebraicGeometry.ProEtaleWeilSheaf
