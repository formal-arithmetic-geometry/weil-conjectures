/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NativeOpenTensorComparisonData
import all Sheaf.Paper.NativeTensorAcyclicTestComparison
import all Sheaf.Paper.NativeTensorModelComparison
import Sheaf.Paper.NativeOpenTensorChains

/-! # Derived open tensor projection

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

/-- The native open tensor projection comparison descends to unbounded derived objects.

Source: Stacks, lemma-j-shriek-and-tensor; native open comparison steps 3--6.
(blueprint: new-sf-native-open-tensor-projection-descent).

Proof: use the product of the K-flat presentations of U and Z. Their acyclic-test
K-flat objects satisfy the two-sided test needed by the tensor models. Extension
and restriction preserve that test by s. Compare each derived tensor with its
cochain model, apply the totalized projection isomorphism, and use the
exact-functor factorization of extension and restriction. The resulting natural
isomorphism descends through the fully faithful whiskering functor for the
product localization. No restriction on boundedness or support is imposed. -/
theorem native_open_tensor_projection_comparison (s : NativeOpenTensorData k₀ l j) :
    Nonempty (nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j) := by
  let R := upperStar k₀ l j
  let E := extensionByZero k₀ l j
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let TU := Functor.uncurry.obj (nativeTensorTotal k₀ l U)
  let TZ := Functor.uncurry.obj (nativeTensorTotal k₀ l Z)
  obtain ⟨_, g, _⟩ := native_open_tensor_chains k₀ l j s
  let PU := NativeTensorKFlat k₀ l U (nativeTensorBifunctor k₀ l U)
  let PZ := NativeTensorKFlat k₀ l Z (nativeTensorBifunctor k₀ l Z)
  let iU := ObjectProperty.ι PU
  let iZ := ObjectProperty.ι PZ
  let qU := iU ⋙ DerivedCategory.Q
  let qZ := iZ ⋙ DerivedCategory.Q
  let WU := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l U) (.up ℤ)).inverseImage iU
  let WZ := (HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l Z) (.up ℤ)).inverseImage iZ
  let : qU.IsLocalization WU := native_flat_localization k₀ l U
  let : qZ.IsLocalization WZ := native_flat_localization k₀ l Z
  have hU (P : ObjectProperty.FullSubcategory PU) : FlatTest k₀ l U (iU.obj P) :=
    native_flat_family k₀ l U P
  have hZ (P : ObjectProperty.FullSubcategory PZ) : FlatTest k₀ l Z (iZ.obj P) :=
    native_flat_family k₀ l Z P
  let rf : DerivedCategory.Q ⋙ nativeOpenPull k₀ l j ≅ Rc ⋙ DerivedCategory.Q :=
    R.mapDerivedCategoryFactors
  let ef : DerivedCategory.Q ⋙ nativeOpenExtension k₀ l j ≅ Ec ⋙ DerivedCategory.Q :=
    E.mapDerivedCategoryFactors
  obtain ⟨mL⟩ := native_tensor_model_comparison k₀ l Z (iU ⋙ Ec) iZ
    (fun P ↦ (FlatTest.extend k₀ l j s _ (hU P)).test) (fun P ↦ (hZ P).test)
  obtain ⟨mA⟩ := native_tensor_model_comparison k₀ l U iU (iZ ⋙ Rc)
    (fun P ↦ (hU P).test) (fun P ↦ (FlatTest.restrict k₀ l j s _ (hZ P)).test)
  exact NativeOpenComparisonProof.descend_projection DerivedCategory.Q DerivedCategory.Q
    Rc Ec (nativeOpenPull k₀ l j) (nativeOpenExtension k₀ l j) TU TZ
    (nativeDerivedTensor k₀ l U) (nativeDerivedTensor k₀ l Z) iU iZ WU WZ rf ef g mL mA

end AlgebraicGeometry.ProEtaleWeilSheaf
