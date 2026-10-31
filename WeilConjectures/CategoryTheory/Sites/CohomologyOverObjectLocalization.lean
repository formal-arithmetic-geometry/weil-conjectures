/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import WeilConjectures.CategoryTheory.Sites.CohomologyOverObjectLocalizationAddEquiv
import WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExactSupplement
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

@[expose] public section

universe u₁

namespace CategoryTheory

open CategoryTheory

/-! # Cohomology over an object is cohomology on its localized site

Source: literature/stacks-project/sites-cohomology.tex, Lemma 03F3
(blueprint: lem-weil-pbc-cohomology-over-object-localization)
-/

/-- (blueprint: lem-weil-pbc-cohomology-over-object-localization)
For a site, the cohomology presheaf evaluated at `W` is canonically identified
with the cohomology on the localized site at its final object. -/
theorem cohomology_over_object_localization
    {C : Type u₁} [Category.{u₁} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u₁}]
    [HasExt.{u₁} (Sheaf J AddCommGrpCat.{u₁})]
    (F : Sheaf J AddCommGrpCat.{u₁}) (W : C) (q : ℕ)
    [HasSheafify (J.over W) AddCommGrpCat.{u₁}]
    [HasExt.{u₁} (Sheaf (J.over W) AddCommGrpCat.{u₁})] :
    Nonempty
      (Sheaf.H' F q W ≅
        Sheaf.H' ((GrothendieckTopology.overPullback J AddCommGrpCat.{u₁} W).obj F) q
          (Over.mk (𝟙 W))) := by
  exact ⟨(cohomology_over_object_localization_addEquiv F W q).some.toAddCommGrpIso⟩

end CategoryTheory
