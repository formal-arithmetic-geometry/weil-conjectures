/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.WeilSheaf.CohomologyProEtale
import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.WeilSheaf.CohomologyNonneg
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.WeilSheaf.OpenClosedTriangle
import WeilConjectures.WeilSheaf.CohomologyAdicConstant
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologicalDimension

/-!
# Compactly supported cohomology of the constant Weil sheaf
@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped AlgebraicGeometry.ProEtale

attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] Compactification.over

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

noncomputable def testA1 (F : ProEtaleWeilSheaf k₀ l X) : Nonempty (
  (DerivedCategory.singleFunctor _ 0 ⋙ (ProEtaleWeilSheaf.extensionByZero k₀ l
        (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i).mapDerivedCategory).obj F ≅
  (ProEtaleWeilSheaf.extensionByZero k₀ l
        (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i ⋙ DerivedCategory.singleFunctor _ 0).obj F) := by
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  exact ⟨((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app F⟩

end WeilSheaf
end AlgebraicGeometry
