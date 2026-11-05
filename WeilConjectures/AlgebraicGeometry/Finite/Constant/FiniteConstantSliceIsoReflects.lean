/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
import WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
import WeilConjectures.Algebra.Homology.FilteredFreeKProjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantSliceDerivedStalkComparison
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Recovering algebraic constant values on a nonempty slice

Source: Stacks Project, Tags 03CY, 0F6B and 05RU.
(blueprint: lem-weil-pbc-finite-constant-slice-iso-reflects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t w
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem ulift_preservesColimits (B : Type t) [CommRing B] :
    PreservesColimitsOfSize.{t, t} (ModuleCat.uliftFunctor.{t + 1, t} B) := by
  let U := forget₂ (ModuleCat.{t + 1} B) AddCommGrpCat.{t + 1}
  have : PreservesColimitsOfSize.{t, t} (ModuleCat.uliftFunctor.{t + 1, t} B ⋙ U) := by
    change PreservesColimitsOfSize.{t, t}
      (forget₂ (ModuleCat.{t} B) AddCommGrpCat.{t} ⋙ AddCommGrpCat.uliftFunctor.{t + 1, t})
    infer_instance
  have : ReflectsColimitsOfSize.{t, t} U :=
    { reflectsColimitsOfShape := fun {_} _ ↦
        reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesColimits_of_reflects_of_preserves _ U

end AlgebraicGeometry.Scheme
