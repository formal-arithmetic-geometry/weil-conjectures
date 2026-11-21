/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
import WeilConjectures.CategoryTheory.LargeHomSolutionSet

/-! Adjoint existence for the universe-enlarged Hom functor. -/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- The fixed Hom functor of any object, with its values lifted to the larger
module universe, has a left adjoint when the derived category has coproducts
of the required size. No separator, full faithfulness or exactness is asserted.

Source: Stacks Project, Lemma 19.14.1 (Tag 0F5S). -/
theorem gabriel_popescu_large_hom_isRightAdjoint
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (G : ShrinkHoms A) :
    ((ShrinkHoms.equivalence.{w} A).functor ⋙ preadditiveCoyonedaObj G ⋙
      ModuleCat.uliftFunctor.{vH, w} (End G)ᵐᵒᵖ).IsRightAdjoint := by
  have : HasCoproducts.{max w vA vH} A :=
    derived_large_coproducts_transfer.{w, uA, vA, vH}
  have : HasCoproducts.{max w vH} A := hasCoproducts_shrink.{max w vH, vA}
  have : HasCoproducts.{max w vH} (ShrinkHoms A) := fun _ =>
    Adjunction.hasColimitsOfShape_of_equivalence (ShrinkHoms.equivalence.{w} A).inverse
  rw [Functor.isRightAdjoint_comp_iff_right]
  apply isRightAdjoint_of_preservesLimits_of_solutionSetCondition
  exact large_hom_solutionSetCondition G

end CategoryTheory
