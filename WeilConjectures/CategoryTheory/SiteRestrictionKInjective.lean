/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SitePerfectModelRestriction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.SiteModuleExtensionByZeroExact

/-! # Restriction to a slice preserves K-injective complexes

## References

* Stacks Project, Cohomology on Sites, restriction of K-injectives to an open.
-/

@[expose] public section
set_option autoImplicit false
universe u v r
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

/-- Slice restriction preserves K-injectives, with an independent ring universe.
Source: Stacks Project, Cohomology on Sites; Modules on Sites, Tags 03DI and 03DJ. -/
theorem overFunctor_preservesKInjectiveComplexes_ofUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}] :
    (overFunctor.{max u v r} R U).PreservesKInjectiveComplexes := by
  obtain ⟨hadd, hlim, hcolim, ⟨adj⟩⟩ := siteModuleExtensionByZero_exact R U
  have := hadd
  have := hlim
  have := hcolim
  exact adj.preservesKInjectiveComplexes

end SheafOfModules
