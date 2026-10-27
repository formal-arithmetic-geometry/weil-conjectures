/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.NativeOpenTensorOperations

/-! # The equivariant sheaf open projection formula

Source: Stacks 0E8I, balanced generators and Frobenius reindexing.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

/-- The two orientations of the sheaf projection formula, with the first
orientation normalized by the specified open unit.

Source: Stacks Project, sites-modules.tex, Tag 0E8I,
lemma-j-shriek-and-tensor; step 2 of the native open tensor argument.
(blueprint: lem-sf-native-open-sheaf-projection-tensor).

Proof: identify the geometric open site with the slice at the open. Its
coefficient sheaf is the restriction of the ambient locally finite function
sheaf. On each factoring object define the map [x] tensor y to
[x tensor y restricted to U]. The slice module tensor generator theorem gives
its inverse, inverse identities and naturality in both sheaves. Frobenius
reindexes the same factoring objects and applies the structure maps to x and y,
so the balanced formula commutes with it; faithful forgetting lifts both maps
and their identities to Weil sheaves. Transposing the inverse across the
specified adjunction sends x to [x] tensor y, followed by the inverse balanced
restriction comparison. This is the displayed normalization; the assumed
underlying unit and counit fix the adjunction used in that calculation.
Exchange the two tensor factors to construct the other orientation, using the
balanced symmetry on each section. Its naturality follows from the same formula.
Empty opens and zero sheaves give the unique zero maps; identity opens give the
ordinary balanced tensor isomorphisms. No assertion about complexes or K-flatness
is used in these constructions. -/
theorem native_open_sheaf_projection_tensor
    (adj : extensionByZero k₀ l j ⊣ upperStar k₀ l j)
    (hu : ∀ M, (adj.unit.app M).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier)
    (hc : ∀ N, (adj.counit.app N).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app N.carrier)
    (rho : ∀ M N : ProEtaleWeilSheaf k₀ l Z,
      (upperStar k₀ l j).obj (tensor k₀ l Z N M) ≅
        tensor k₀ l U ((upperStar k₀ l j).obj N) ((upperStar k₀ l j).obj M))
    (hrho : ∀ M N, HEq ((rho M N).hom.hom.f)
      ((ProEtale.adicUpperStarTensorLeftIso l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) N.carrier).hom.app M.carrier)) :
    ∃ gamma : ∀ (M : ProEtaleWeilSheaf k₀ l U) (N : ProEtaleWeilSheaf k₀ l Z),
      tensor k₀ l Z N ((extensionByZero k₀ l j).obj M) ≅
        (extensionByZero k₀ l j).obj (tensor k₀ l U ((upperStar k₀ l j).obj N) M),
      (∀ M N, HEq (adj.homEquiv _ _ ((gamma M N).inv))
        ((tensorFunctor k₀ l U ((upperStar k₀ l j).obj N)).map (adj.unit.app M) ≫
          (rho ((extensionByZero k₀ l j).obj M) N).inv)) ∧
      Nonempty (nativeOpenSheafLeft k₀ l j ≅ nativeOpenSheafRight k₀ l j) ∧
      Nonempty ((𝟭 (ProEtaleWeilSheaf k₀ l Z)).prod (extensionByZero k₀ l j) ⋙
          nativeOpenSheafTensor k₀ l Z ≅
        (upperStar k₀ l j).prod (𝟭 (ProEtaleWeilSheaf k₀ l U)) ⋙ nativeOpenSheafTensor k₀ l U ⋙
          extensionByZero k₀ l j) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
