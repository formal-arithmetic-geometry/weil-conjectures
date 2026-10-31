/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeOpenTensorComparisonData
import WeilConjectures.AlgebraicGeometry.NativeOpenTensorChainRestriction
import WeilConjectures.AlgebraicGeometry.NativeOpenTensorChainProjection

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

attribute [local irreducible] nativeTensorTotal upperStar

/-- Totalizing the native restriction and projection comparisons gives natural
isomorphisms of unbounded cochain functors.

Source: Stacks 0GL1, 012Z and 0E8I; steps 3--4 of the native open tensor proof.
(blueprint: new-sf-native-open-tensor-chains).

Proof: the restriction comparison is natural by its normalized underlying module
map. Curry it and totalize degreewise. Restriction is a left adjoint, so it
preserves the diagonal coproducts; the comparison and its inverse commute with
the two differentials and their Koszul signs. For projection, use the natural
sheaf projection isomorphism and totalize its inverse. Extension is a left
adjoint and likewise preserves the diagonal coproducts. The total-comparison
naturality theorem gives naturality in both complexes. No resolutions or
localization are used here. -/
theorem native_open_tensor_chains (s : NativeOpenTensorData k₀ l j) :
    ∃ (_r : Functor.uncurry.obj (nativeTensorTotal k₀ l Z) ⋙
          (upperStar k₀ l j).mapHomologicalComplex (.up ℤ) ≅
        ((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).prod
          ((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)) ⋙
            Functor.uncurry.obj (nativeTensorTotal k₀ l U))
      (_g : ((extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)).prod (𝟭 _) ⋙
          Functor.uncurry.obj (nativeTensorTotal k₀ l Z) ≅
        (𝟭 _).prod ((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj (nativeTensorTotal k₀ l U) ⋙
            (extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)), True := by
  obtain ⟨r⟩ := native_open_tensor_chain_restriction k₀ l j s
  obtain ⟨g⟩ := native_open_tensor_chain_projection k₀ l j s
  exact ⟨r, g, trivial⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
