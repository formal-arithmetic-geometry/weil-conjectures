/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeOpenTensorComparisonData
import all WeilConjectures.AlgebraicGeometry.NativeOpenTensorSheafComparisons
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-! # Native open tensor comparisons on complexes

Source: Stacks 0GL1, 012Z and 0E8I; native open tensor proof steps 3--4.

The normalized restriction maps assemble to a natural sheaf comparison.
Totalizing it and the natural sheaf projection comparison gives the two
isomorphisms of unbounded cochain functors, before localization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Mod.tensorLeft
  CategoryTheory.Mod.ihomAdjunction
  AlgebraicGeometry.ProEtaleWeilSheaf.tensorIhomAdjunction

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

attribute [local irreducible] nativeTensorTotal upperStar nativeTensorBifunctor
  extensionByZero Functor.mapHomologicalComplex

/-- Restriction commutes with the native total cochain tensor.
Source: Stacks 012Z and 0E8I (blueprint: new-sf-native-open-tensor-chain-restriction).
Proof: totalize the natural sheaf restriction comparison. Restriction preserves
all diagonal coproducts since it is a left adjoint; the total comparison API
supplies inverse identities, differential compatibility, and naturality. -/
theorem native_open_tensor_chain_restriction (s : NativeOpenTensorData k₀ l j) :
    Nonempty (Functor.uncurry.obj (nativeTensorTotal k₀ l Z) ⋙
      (upperStar k₀ l j).mapHomologicalComplex (.up ℤ) ≅
        ((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).prod
          ((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)) ⋙
            Functor.uncurry.obj (nativeTensorTotal k₀ l U)) := by
  let R := upperStar k₀ l j
  have : R.IsLeftAdjoint := (upperStarLowerStarAdjunction k₀ l j).isLeftAdjoint
  obtain ⟨r⟩ := (native_open_tensor_sheaf_comparisons k₀ l j s).1
  exact NativeOpenChainProof.restrictionTotal R
    (nativeTensorBifunctor k₀ l U).flip (nativeTensorBifunctor k₀ l Z).flip
    (nativeTensorTotal k₀ l U) (nativeTensorTotal k₀ l Z)
    (nativeTotal_eq k₀ l U)
    (nativeTotal_eq k₀ l Z) r

end AlgebraicGeometry.ProEtaleWeilSheaf
