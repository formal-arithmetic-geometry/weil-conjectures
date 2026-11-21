/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Restriction to a localized ringed site preserves K-injectivity

## References

* Stacks Project, Tag 08FI (Lemma 21.20.1), also used in Tag 0A94
-/

@[expose] public section

universe u v r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction of a K-injective module complex to C/U is K-injective, for any
Grothendieck topology on C. -/
theorem isKInjective_restrict_localizedOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{max u v r}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v r} R U).PreservesZeroMorphisms)
    (I : CochainComplex (SheafOfModules.{max u v r} R) ℤ) [I.IsKInjective] :
    letI := hzero
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{max u v r} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let := hzero
  obtain ⟨G, hlimits, hcolimits, hadd, ⟨adj⟩⟩ :=
    localized_restriction_adjunctionOfUniverses.{u, v, r} R U hzero
  let : PreservesFiniteLimits G := hlimits
  let : PreservesFiniteColimits G := hcolimits
  let : G.IsLeftAdjoint := adj.isLeftAdjoint
  let : G.Additive := G.additive_of_preserves_binary_products
  let : (SheafOfModules.overFunctor.{max u v r} R U).Additive := hadd
  let : (SheafOfModules.overFunctor.{max u v r} R U).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map I

end CategoryTheory
