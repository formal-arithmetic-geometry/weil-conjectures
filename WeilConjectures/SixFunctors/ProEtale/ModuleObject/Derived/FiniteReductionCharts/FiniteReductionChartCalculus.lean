/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Ordered tensor and shift charts for condensed coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.md, proof Step 2 (twists and derived tensor).
(blueprint: def-pur-finite-reduction-chart-calculus).

The native coefficients are the ring objects `Λ_X = p_X^* Λ`, and the tensor is
`CondensedRing.derivedTensor` on the unbounded category `D(Mod_{Λ_X})`. The ordered
recursion uses the specified zero and line charts. Its unit step and the comparison
for an exact monoidal functor are explicit composites of existing canonical maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteReductionCharts

/-- Ordered chart recursion: the zero chart is `z`; each successor first uses `s`,
tensors the preceding chart with `t`, and applies `a`. No coherence map is chosen.
Source: finite-reduction proof, Step 2, ordered twist comparisons
(blueprint: def-pur-finite-reduction-chart-calculus). -/
def orderedPower {C : Type v₁} [Category.{w₁} C]
    (T : C ⥤ C ⥤ C) (B U : ℕ → C) (L V : C)
    (z : B 0 ≅ U 0) (t : L ≅ V)
    (s : ∀ n : ℕ, B (n + 1) ≅ (T.obj (B n)).obj L)
    (a : ∀ n : ℕ, (T.obj (U n)).obj V ≅ U (n + 1)) :
    ∀ n : ℕ, B n ≅ U n
  | 0 => z
  | n + 1 => s n ≪≫
      (T.mapIso (orderedPower T B U L V z t s a n)).app L ≪≫
        (T.obj (U n)).mapIso t ≪≫ a n

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

local notation "M" => Mod _ (condensedRingObj Λ X)
local notation "D" => _root_.DerivedCategory M

/-- Tensoring any native derived object with a shifted unit: use the K-flat
second-variable shift comparison and then the shifted right unitor.
Source: finite-reduction proof, Step 2, shift and tensor-unit comparison
(blueprint: def-pur-finite-reduction-chart-calculus). -/
def tensorUnit (K : D) (r : ℤ) :
    ((derivedTensor Λ X).obj K).obj ((𝟙_ D) ⟦r⟧) ≅ K⟦r⟧ :=
  letI := _root_.DerivedCategory.commShiftTensorLeft M K
  (((curriedTensor D).obj K).commShiftIso r).app (𝟙_ D) ≪≫
    (shiftFunctor D r).mapIso (ρ_ K)

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteReductionCharts

namespace CategoryTheory.Functor

end CategoryTheory.Functor
