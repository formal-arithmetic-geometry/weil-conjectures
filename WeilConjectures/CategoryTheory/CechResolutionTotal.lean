/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CechResolutionDoubleComplex
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.CategoryTheory.InjectiveCechTotalSections
import WeilConjectures.CategoryTheory.ResolutionSectionCohomology

/-!
# Total cohomology of the Čech resolution double complex

Source: Stacks Project Tags 03AW
and 03F6.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- The total Čech complex of an injective resolution computes sheaf cohomology.

Source: Stacks Project Tags 03AW and 03F6. -/
theorem Sheaf.cechResolutionDoubleComplex_total
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X) (n : ℕ) :
    Nonempty (((Sheaf.cechResolutionDoubleComplex I X π).total
      (ComplexShape.up ℕ)).homology n ≅ F.H' n X) := by
  obtain ⟨e⟩ := injective_cech_total_sections I.cocomplex
    (fun q ↦ inferInstance) X π hπ n
  obtain ⟨f⟩ := Sheaf.resolution_section_cohomology I X n
  exact ⟨e ≪≫ f⟩

end CategoryTheory
