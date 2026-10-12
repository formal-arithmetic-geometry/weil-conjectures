module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Over
import Sheaf.Paper.SiteRestrictionInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

@[expose] public section

universe u₁

namespace CategoryTheory

/-- Additive equivalence underlying the comparison of cohomology over an object
with cohomology on the localized site.

This is the chain-level comparison induced by restricting an injective resolution
along the slice localization; its construction follows Stacks Project, Lemma 03F3.
(blueprint: lem-weil-pbc-cohomology-over-object-localization-addEquiv)

Proof: Restrict an injective resolution along the localized-site restriction.
Use exactness and preservation of injectives, then identify the resulting section complexes.
Taking cohomology yields the additive equivalence.
-/
theorem cohomology_over_object_localization_addEquiv
    {C : Type u₁} [Category.{u₁} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u₁}]
    [HasExt.{u₁} (Sheaf J AddCommGrpCat.{u₁})]
    (F : Sheaf J AddCommGrpCat.{u₁}) (W : C) (q : ℕ)
    [HasSheafify (J.over W) AddCommGrpCat.{u₁}]
    [HasExt.{u₁} (Sheaf (J.over W) AddCommGrpCat.{u₁})] :
    Nonempty ((Sheaf.H' F q W) ≃+ Sheaf.H'
      ((GrothendieckTopology.overPullback J AddCommGrpCat.{u₁} W).obj F) q (Over.mk (𝟙 W))) := by
  sorry

end CategoryTheory
