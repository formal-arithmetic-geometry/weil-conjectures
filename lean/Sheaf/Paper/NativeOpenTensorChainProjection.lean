/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NativeOpenTensorComparisonData
import all Sheaf.Paper.NativeOpenTensorSheafComparisons

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

/-- The native cochain projection comparison.
Source: Stacks 012Z and 0E8I (blueprint: new-sf-native-open-tensor-chain-projection).
Proof: totalize the inverse natural sheaf projection comparison and invert the
result. Extension preserves all diagonal coproducts since it is a left adjoint;
the total comparison API supplies naturality and differential compatibility. -/
theorem native_open_tensor_chain_projection (s : NativeOpenTensorData k₀ l j) :
    Nonempty (((extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)).prod (𝟭 _) ⋙
      Functor.uncurry.obj (nativeTensorTotal k₀ l Z) ≅
        (𝟭 _).prod ((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj (nativeTensorTotal k₀ l U) ⋙
            (extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)) := by
  let R := upperStar k₀ l j
  let E := extensionByZero k₀ l j
  have : E.IsLeftAdjoint := s.adj.isLeftAdjoint
  obtain ⟨g⟩ := (native_open_tensor_sheaf_comparisons k₀ l j s).2
  exact NativeOpenChainProof.projectionTotal R E
    (nativeTensorBifunctor k₀ l U).flip (nativeTensorBifunctor k₀ l Z).flip
    (nativeTensorTotal k₀ l U) (nativeTensorTotal k₀ l Z)
    (nativeTotal_eq k₀ l U)
    (nativeTotal_eq k₀ l Z) g

end AlgebraicGeometry.ProEtaleWeilSheaf
