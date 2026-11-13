/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact

/-!
# Extension by zero and restriction on a localized site

## References

* [Stacks Project, Tag 03DH](https://stacks.math.columbia.edu/tag/03DH)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction to a localized site has an exact extension-by-zero left adjoint,
and is itself exact.
-/
theorem siteRestriction_injectives
    {C : Type w} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C) :
    Nonempty
        (Functor.sheafPullbackConstruction.sheafPullback
            (Over.forget W) AddCommGrpCat.{w} (J.toGrothendieck.over W)
            J.toGrothendieck ⊣
          J.toGrothendieck.overPullback AddCommGrpCat.{w} W) ∧
      (∃ (hL : (Functor.sheafPullbackConstruction.sheafPullback
          (Over.forget W) AddCommGrpCat.{w} (J.toGrothendieck.over W)
          J.toGrothendieck).PreservesZeroMorphisms),
        ∀ (S : ShortComplex (Sheaf (J.toGrothendieck.over W) AddCommGrpCat.{w})),
          S.ShortExact →
            (@ShortComplex.map _ _ _ _ _ _ S
              (Functor.sheafPullbackConstruction.sheafPullback
                (Over.forget W) AddCommGrpCat.{w}
                (J.toGrothendieck.over W) J.toGrothendieck) hL).ShortExact) ∧
      (∀ (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{w})),
        S.ShortExact →
          (S.map (J.toGrothendieck.overPullback AddCommGrpCat.{w} W)).ShortExact) := by
  refine ⟨⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.forget W) AddCommGrpCat (J.toGrothendieck.over W) J.toGrothendieck⟩, ?_, ?_⟩
  · exact site_extensionByZero_exact J W
  · intro S hS
    exact siteRestriction_exact J W S hS

end CategoryTheory
