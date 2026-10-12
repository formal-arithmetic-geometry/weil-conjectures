module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Over
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalizationAddEquiv
import Sheaf.Paper.SiteRestrictionInjectives
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
