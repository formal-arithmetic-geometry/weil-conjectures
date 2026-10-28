/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NativeOpenTensorComparisonData
import all Sheaf.Paper.NativeTensorAcyclicTestComparison
import all Sheaf.Paper.NativeTensorModelComparison
import Sheaf.Paper.NativeOpenTensorChains

/-! # Derived open restriction and tensor

Source: Stacks 0GL1 and 06YN; native open tensor localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u
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

attribute [local irreducible] nativeDerivedTensor nativeTensorTotal NativeIsKFlat
  nativeTensorBifunctor Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  upperStar extensionByZero Functor.mapHomologicalComplex

/-- Exact open restriction commutes naturally with the native derived tensor.

Source: Stacks, lemma-pullback-tensor-product, native open comparison steps 3--6.
(blueprint: new-sf-native-open-tensor-restriction-descent).

Proof: restrict the derived-category quotient to acyclic-test K-flat Z-complexes.
These present the whole derived category. The cone criterion converts their
acyclic test to the two-sided test used by the tensor models, and s preserves
that test under restriction. Apply the natural model isomorphisms before and
after restriction, and place the cochain restriction comparison between them.
The exact-functor factorization identifies termwise and derived restriction.
Whiskering along the product localization is fully faithful, so this natural
isomorphism descends to arbitrary pairs of derived objects. -/
theorem native_open_tensor_restriction_comparison (s : NativeOpenTensorData k₀ l j) :
    Nonempty (nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
      (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U) := by
  let R := upperStar k₀ l j
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let TU := Functor.uncurry.obj (nativeTensorTotal k₀ l U)
  let TZ := Functor.uncurry.obj (nativeTensorTotal k₀ l Z)
  obtain ⟨r, _, _⟩ := native_open_tensor_chains k₀ l j s
  let PZ := NativeTensorKFlat k₀ l Z (nativeTensorBifunctor k₀ l Z)
  let iZ := ObjectProperty.ι PZ
  let qZ := iZ ⋙ DerivedCategory.Q
  let WZ := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l Z) (.up ℤ)).inverseImage iZ
  let : qZ.IsLocalization WZ := native_flat_localization k₀ l Z
  have hZ (P : ObjectProperty.FullSubcategory PZ) : FlatTest k₀ l Z (iZ.obj P) :=
    native_flat_family k₀ l Z P
  let rf : DerivedCategory.Q ⋙ nativeOpenPull k₀ l j ≅ Rc ⋙ DerivedCategory.Q :=
    R.mapDerivedCategoryFactors
  obtain ⟨mB⟩ := native_tensor_model_comparison k₀ l Z iZ iZ
    (fun P ↦ (hZ P).test) (fun P ↦ (hZ P).test)
  obtain ⟨mR⟩ := native_tensor_model_comparison k₀ l U (iZ ⋙ Rc) (iZ ⋙ Rc)
    (fun P ↦ (FlatTest.restrict k₀ l j s _ (hZ P)).test)
    (fun P ↦ (FlatTest.restrict k₀ l j s _ (hZ P)).test)
  exact NativeOpenComparisonProof.descend_restriction DerivedCategory.Q DerivedCategory.Q
    Rc (nativeOpenPull k₀ l j) TU TZ (nativeDerivedTensor k₀ l U)
    (nativeDerivedTensor k₀ l Z) iZ WZ rf r mB mR

end AlgebraicGeometry.ProEtaleWeilSheaf
